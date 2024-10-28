-- \/\/\/ DO NOT MODIFY THE FOLLOWING LINES \/\/\/
module SudokuSolver(Board, Solutions(..), author, nickname, numSolutions) where
import Sudoku(Board, Solutions(..))


-- /\/\/\ DO NOT MODIFY THE PRECEDING LINES /\/\/\


import Data.List (delete, minimumBy, sortBy, (\\), nub)
import Data.Ord (comparing)
import Control.Monad (guard, msum, foldM, unless)
import Data.Maybe (isNothing, fromJust, fromMaybe)
import qualified Data.Map.Strict as Map
import Control.Applicative ((<|>))
import Data.Tuple (swap)
import Data.Bifunctor (second)
import qualified Data.Set as Set



{- (Remember to provide a brief (about 100-500 words) description of
   your implementation.)
 -}


author :: String
author = "Aoping Lyu"  -- replace `undefined' with your first and last name

nickname :: String
nickname = "SudokuOuSama-Backtracking" -- replace `undefined' with a nickname for your solver



{- PossibleValues represents the possible values for each unassigned cell.
   It maps cell positions (row, column) to a list of possible values [Int].
   INVARIANT: Each list of possible values is non-empty and contains integers between 1 and n (inclusive).
 -}
type PossibleValues = Map.Map (Int, Int) [Int]

{- Arc represents a directed arc between two cells in the context of the AC-3 algorithm.
   It is a pair of cell positions ((Int, Int), (Int, Int)).
 -}
type Arc = ((Int, Int), (Int, Int))

{- n board
   Returns the size of the Sudoku board, i.e., the number of rows or columns.
   PRE: The board is a square matrix (list of lists) with equal number of rows and columns.
   RETURNS: The length of the board, which is the size of the Sudoku grid.
 -}
n :: Board -> Int
n board = length board

{- blockSize board
   Calculates the size of the block in the Sudoku board.
   PRE: The size of the board n is a perfect square.
   RETURNS: The size of the block, which is sqrt(n).
 -}
blockSize :: Board -> Int
blockSize board = round (sqrt (fromIntegral (n board)))

{- getRow board row
   Retrieves the values in the specified row of the board.
   PRE: 0 <= row < n, where n is the size of the board.
   RETURNS: A list of integers representing the values in the row.
 -}
getRow :: Board -> Int -> [Int]
getRow board row = board !! row

{- getCol board col
   Retrieves the values in the specified column of the board.
   PRE: 0 <= col < n, where n is the size of the board.
   RETURNS: A list of integers representing the values in the column.
 -}
getCol :: Board -> Int -> [Int]
getCol board col = [board !! r !! col | r <- [0..n board - 1]]

{- getBlock board row col
   Retrieves the values in the block containing the cell at (row, col).
   PRE: 0 <= row, col < n, where n is the size of the board.
   RETURNS: A list of integers representing the values in the block.
 -}
getBlock :: Board -> Int -> Int -> [Int]
getBlock board row col =
  [ board !! r !! c
  | r <- [startRow..startRow + blockSize board - 1]
  , c <- [startCol..startCol + blockSize board - 1]
  ]
  where
    startRow = (row `div` blockSize board) * blockSize board
    startCol = (col `div` blockSize board) * blockSize board

{- neighbors board row col
   Finds all the neighboring cells of the cell at (row, col), i.e.,
   cells in the same row, column, or subgrid, excluding the cell itself.
   PRE: 0 <= row, col < n, where n is the size of the board.
   RETURNS: A list of (Int, Int) positions of neighboring cells.
 -}
neighbors :: Board -> Int -> Int -> [(Int, Int)]
neighbors board row col = nub $
    [(row, c) | c <- [0..n board - 1], c /= col] ++
    [(r, col) | r <- [0..n board - 1], r /= row] ++
    [ (r, c) |
      r <- [startRow..startRow + blockSize board - 1],
      c <- [startCol..startCol + blockSize board - 1],
      (r, c) /= (row, col)
    ]
  where
    startRow = (row `div` blockSize board) * blockSize board
    startCol = (col `div` blockSize board) * blockSize board

{- revise pv (xi, xj) (xk, xl)
   Applies the AC-3 revise step to eliminate inconsistent values from xi's possible values.
   PRE: pv contains possible values for cells (xi, xj) and (xk, xl).
   RETURNS: Just pv' where pv' is the updated PossibleValues map with (xi, xj)'s possible values revised,
            or Nothing if no revision was necessary.
 -}
revise :: PossibleValues -> (Int, Int) -> (Int, Int) -> Maybe PossibleValues
revise pv (xi, xj) (xk, xl) = do
    xiVals <- Map.lookup (xi, xj) pv
    xkVals <- Map.lookup (xk, xl) pv
    let xiVals' = [v | v <- xiVals, any (/= v) xkVals]  -- Eliminate values inconsistent with (xk, xl)
    if xiVals' /= xiVals then
      Just $ Map.insert (xi, xj) xiVals' pv
    else
      Just pv  -- No revision needed

{- possibleValuesAt board row col
   Computes the possible values for the cell at (row, col) based on current board.
   PRE: 0 <= row, col < n, where n is the size of the board.
        The cell at (row, col) is empty (i.e., contains 0).
   RETURNS: A list of integers representing possible values for the cell,
            i.e., values not already present in the same row, column, or subgrid.
 -}
possibleValuesAt :: Board -> Int -> Int -> [Int]
possibleValuesAt board row col = [1..n board] \\ takenValues
  where
    takenValues = getRow board row ++ getCol board col ++ getBlock board row col

{- initializePossibleValues board
   Initializes the PossibleValues map for all empty cells in the board.
   RETURNS: A PossibleValues map mapping each empty cell to its possible values.
 -}
initializePossibleValues :: Board -> PossibleValues
initializePossibleValues board = Map.fromList [((r, c), possibleValuesAt board r c) | r <- [0..n board - 1], c <- [0..n board - 1], board !! r !! c == 0]

{- updatePossibleValues board pv row col val
   Updates the PossibleValues map after placing val at (row, col) in the board.
   PRE: val is placed at position (row, col) in the board.
   RETURNS: A new PossibleValues map with possible values updated for affected cells.
 -}
updatePossibleValues :: Board -> PossibleValues -> Int -> Int -> Int -> PossibleValues
updatePossibleValues board pv row col val = foldl updateCell pv affectedCells
  where
    n' = n board
    subSize = blockSize board
    affectedCells = [(row, c) | c <- [0..n' -1], c /= col] ++
                    [(r, col) | r <- [0..n' -1], r /= row] ++
                    [ (r, c) |
                      r <- [startRow..startRow + subSize -1],
                      c <- [startCol..startCol + subSize -1],
                      (r, c) /= (row, col)
                    ]
    startRow = (row `div` subSize) * subSize
    startCol = (col `div` subSize) * subSize
    updateCell acc (r, c) = Map.adjust (delete val) (r, c) acc

{- updateBoard board row col val
   Places val at position (row, col) in the board.
   RETURNS: A new board with val placed at (row, col).
 -}
updateBoard :: Board -> Int -> Int -> Int -> Board
updateBoard board row col val =
  [ [ if r == row && c == col then val else board !! r !! c
    | c <- [0..n board - 1] ]
  | r <- [0..n board - 1] ]

{- placeValue board pv row col val
   Places val at (row, col) in the board and updates the PossibleValues map.
   RETURNS: A tuple (board', pv') where:
            - board' is the updated board.
            - pv' is the updated PossibleValues map with (row, col) removed and affected cells updated.
 -}
placeValue :: Board -> PossibleValues -> Int -> Int -> Int -> (Board, PossibleValues)
placeValue board pv row col val =
  let board' = updateBoard board row col val
      pv' = Map.delete (row, col) pv
      pv'' = updatePossibleValues board' pv' row col val
  in (board', pv'')

{- selectMRVCell pv
   Selects the unassigned cell with Minimum Remaining Values (MRV) heuristic.
   RETURNS: Just (row, col) of the cell with the fewest possible values,
            or Nothing if no unassigned cells remain.
 -}
selectMRVCell :: PossibleValues -> Maybe (Int, Int)
selectMRVCell pv
  | Map.null pv = Nothing
  | otherwise = Just $ fst $ minimumBy (comparing (length . snd)) (Map.toList pv)

{- orderValues board pv row col
   Orders the possible values for cell (row, col) using the Least Constraining Value (LCV) heuristic.
   RETURNS: A list of possible values for (row, col), ordered from least constraining to most constraining.
 -}
orderValues :: Board -> PossibleValues -> Int -> Int -> [Int]
orderValues board pv row col =
  let values = fromJust $ Map.lookup (row, col) pv
  in sortBy (comparing (constraintCount board pv row col)) values

{- constraintCount board pv row col val
   Calculates the number of constraints imposed on neighboring cells if val is assigned to (row, col).
   RETURNS: An integer representing the sum of possible values in the PossibleValues map after assignment.
 -}
constraintCount :: Board -> PossibleValues -> Int -> Int -> Int -> Int
constraintCount board pv row col val =
  let (board', pvAfter) = placeValue board pv row col val
      affectedCells = Map.keys pvAfter
  in sum [length $ fromMaybe [] (Map.lookup (r, c) pvAfter) | (r, c) <- affectedCells]


{- isSolved board
   Checks if the Sudoku board is completely filled (no zeros).
   RETURNS: True if the board has no empty cells; False otherwise.
 -}
isSolved :: Board -> Bool
isSolved = all (notElem 0)

{- isUnique xs
   Checks if the list xs contains unique non-zero values.
   RETURNS: True if all non-zero values in xs are unique; False otherwise.
 -}
isUnique :: [Int] -> Bool
isUnique xs = let nonZeroValues = filter (/= 0) xs in length nonZeroValues == length (nub nonZeroValues)


{- isValidSolution board
   Checks if the Sudoku board is valid, i.e., all rows, columns, and subgrids contain unique non-zero values.
   RETURNS: True if the board is valid; False otherwise.
 -}
isValidSolution :: Board -> Bool
isValidSolution board =
    all isUnique [getRow board r | r <- [0..n board - 1]] &&
    all isUnique [getCol board c | c <- [0..n board - 1]] &&
    all isUnique [getBlock board r c | r <- [0, blockSize board .. n board - 1], c <- [0, blockSize board .. n board - 1]]


{- solveSudoku board pv
   Solves the Sudoku puzzle using backtracking and constraint propagation.
   PRE: The board and pv are consistent, i.e., possible values in pv respect the current board state.
   RETURNS: Just solvedBoard if a solution is found; Nothing if no solution exists.
   VARIANT: The number of unassigned cells (size of pv).
 -}
solveSudoku :: Board -> PossibleValues -> Maybe Board
solveSudoku board pv
  | isSolved board = Just board
  | otherwise = case selectMRVCell pv of
      Nothing -> Nothing
      Just (row, col) -> 
          let orderedValues = orderValues board pv row col
          in msum $ map (tryValue row col) orderedValues
  where
    {- tryValue row col val
       Attempts to assign 'val' to the cell at position (row, col) and recursively solve the Sudoku.
       PRE:
         - (row, col) is an unassigned cell in the board.
         - 'val' is a possible value for (row, col) in the PossibleValues map.
       RETURNS:
         - Just solvedBoard if a valid solution is found after assigning 'val' at (row, col).
         - Nothing if assigning 'val' leads to a dead end or inconsistency.
       VARIANT:
         - The number of unassigned cells (size of pv).
       EXAMPLES:
         - If assigning 'val' at (row, col) results in a valid solution, returns Just solvedBoard.
         - If assigning 'val' at (row, col) causes a conflict, returns Nothing.
     -}
    tryValue :: Int -> Int -> Int -> Maybe Board
    tryValue row col val = 
      let (board', pv') = placeValue board pv row col val
          neighbors' = neighbors board row col -- Find neighbors of the selected MRV cell
          reducedArcs = Set.fromList [((xi, xj), (xk, xl)) | (xi, xj) <- (row, col) : neighbors', (xk, xl) <- neighbors' ]
      in case ac3 board' pv' reducedArcs of
          Nothing -> Nothing  -- Inconsistency found, backtrack
          Just pv'' ->
            if any null (Map.elems pv'') then
              Nothing  -- Dead end
            else
              solveSudoku board' pv''

{- ac3 board pv queue
   Enforces arc consistency on the PossibleValues map using the AC-3 algorithm.
   PRE: queue is a set of arcs to process.
   RETURNS: Just pv' where pv' is the revised PossibleValues map, or Nothing if inconsistency is found.
   VARIANT: The size of the queue.
 -}
ac3 :: Board -> PossibleValues -> Set.Set Arc -> Maybe PossibleValues
ac3 board pv queue
  | Set.null queue = Just pv  -- If the queue is empty, return the consistent possible values
  | otherwise = do
      let ((xi, xj), (xk, xl)) = Set.findMin queue
          q' = Set.delete ((xi, xj), (xk, xl)) queue
      case revise pv (xi, xj) (xk, xl) of
        Just pv'' ->  -- If revision was made
          if null (fromJust $ Map.lookup (xi, xj) pv'') then
            Nothing  -- Failure: a cell has no possible values
          else
            let newArcs = Set.fromList [((xm, xn), (xi, xj)) |
                          (xm, xn) <- neighbors board xi xj,
                          (xm, xn) /= (xk, xl)]
                q'' = Set.union q' newArcs
            in ac3 board pv'' q''
        Nothing -> ac3 board pv q'

{- countSolutions board pv acc maxSolutions
   Counts the number of solutions for the Sudoku puzzle, up to maxSolutions.
   PRE: The board and pv are consistent.
   RETURNS: The number of solutions found, up to maxSolutions.
   VARIANT: The number of unassigned cells (size of pv).
 -}
countSolutions :: Board -> PossibleValues -> Int -> Int -> Int
countSolutions board pv acc maxSolutions
  | acc >= maxSolutions = acc  -- Stop early if maxSolutions found
  | isSolved board && isValidSolution board = acc + 1
  | otherwise = case selectMRVCell pv of
      Nothing -> acc
      Just (row, col) -> 
          let orderedValues = orderValues board pv row col
          in foldl tryValue acc orderedValues
        where
          tryValue acc' val
            | acc' >= maxSolutions = acc'  -- Early exit
            | otherwise = 
                let (board', pv') = placeValue board pv row col val
                in if any null (Map.elems pv') then
                     acc'  -- Dead end
                   else
                     countSolutions board' pv' acc' maxSolutions

{- numSolutions board
   Determines the number of solutions for the given Sudoku board.
   RETURNS: 
     - NoSolution if there are no solutions.
     - UniqueSolution if there is exactly one solution.
     - MultipleSolutions if there are multiple solutions.
 -}
numSolutions :: Board -> Solutions
numSolutions board = 
    let pv = initializePossibleValues board
        maxSolutions = 2  -- Limit the number of solutions to 2
    in case countSolutions board pv 0 maxSolutions of
        0 -> NoSolution
        1 -> UniqueSolution
        _ -> MultipleSolutions

{- IO added for testing-}
-- main :: IO ()
-- instance Show Solutions where
--     show NoSolution = "NoSolution"
--     show UniqueSolution = "UniqueSolution"
--     show MultipleSolutions = "MultipleSolutions"
