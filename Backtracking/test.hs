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
import System.CPUTime ( getCPUTime ) -- For timing
import Data.Tuple (swap)
import Data.Bifunctor (second)
import qualified Data.Set as Set


import System.Random (randomRIO)

import TestBoards (
    uniques, ambiguouss, invalids,
    uniqueBoard1, uniqueBoard2, uniqueBoard3, uniqueBoard4, uniqueBoard5,
    uniqueBoard6, uniqueBoard7, uniqueBoard8, uniqueBoard9,
    uniqueBoardA, uniqueBoardB, uniqueBoardC,
    ambiguousBoard1, ambiguousBoard2, ambiguousBoard3, ambiguousBoard4, ambiguousBoard5,
    ambiguousBoard6, ambiguousBoard7, ambiguousBoard8, ambiguousBoard9,
    ambiguousBoardA, ambiguousBoardB, ambiguousBoardC,
    invalidBoard1, invalidBoard2, invalidBoard3, invalidBoard4, invalidBoard5,
    invalidBoard6, invalidBoard7, invalidBoard8, invalidBoard9,
    invalidBoardA, invalidBoardB, invalidBoardC)

import TestCases (board0, board1, board2, board3, board4, board5, board6, board7, board10)

author :: String
author = "Aoping Lyu"  -- replace `undefined' with your first and last name

nickname :: String
nickname = "SudokuOuSama" -- replace `undefined' with a nickname for your solver

-- Define PossibleValues as a map from cell positions to possible values
type PossibleValues = Map.Map (Int, Int) [Int]
type Arc = ((Int, Int), (Int, Int))


-- Define the size of the Sudoku board
n :: Board -> Int
n board = length board

-- Define the size of the subgrid
subGridSize :: Board -> Int
subGridSize board = round (sqrt (fromIntegral (n board)))

-- Get the values in a row
getRow :: Board -> Int -> [Int]
getRow board row = board !! row

-- Get the values in a column
getCol :: Board -> Int -> [Int]
getCol board col = [board !! r !! col | r <- [0..n board - 1]]

-- Get the values in a subgrid
getSubGrid :: Board -> Int -> Int -> [Int]
getSubGrid board row col =
  [ board !! r !! c
  | r <- [startRow..startRow + subGridSize board - 1]
  , c <- [startCol..startCol + subGridSize board - 1]
  ]
  where
    startRow = (row `div` subGridSize board) * subGridSize board
    startCol = (col `div` subGridSize board) * subGridSize board

-- Find neighbors of a cell (row, col)
neighbors :: Board -> Int -> Int -> [(Int, Int)]
neighbors board row col = nub $
    [(row, c) | c <- [0..n board - 1], c /= col] ++
    [(r, col) | r <- [0..n board - 1], r /= row] ++
    [ (r, c) |
      r <- [startRow..startRow + subGridSize board - 1],
      c <- [startCol..startCol + subGridSize board - 1],
      (r, c) /= (row, col)
    ]
  where
    startRow = (row `div` subGridSize board) * subGridSize board
    startCol = (col `div` subGridSize board) * subGridSize board

-- Revise possible values at (xi, xj) based on (xk, xl)
revise :: PossibleValues -> (Int, Int) -> (Int, Int) -> Maybe PossibleValues
revise pv (xi, xj) (xk, xl) = do
    xiVals <- Map.lookup (xi, xj) pv
    xkVals <- Map.lookup (xk, xl) pv
    let xiVals' = [v | v <- xiVals, any (/= v) xkVals]  -- Eliminate values inconsistent with (xk, xl)
    if xiVals' /= xiVals then
      Just $ Map.insert (xi, xj) xiVals' pv
    else
      Just pv  -- No revision needed

-- Possible values at a cell
possibleValuesAt :: Board -> Int -> Int -> [Int]
possibleValuesAt board row col = [1..n board] \\ takenValues
  where
    takenValues = getRow board row ++ getCol board col ++ getSubGrid board row col

-- Initialize PossibleValues map
initializePossibleValues :: Board -> PossibleValues
initializePossibleValues board = Map.fromList [((r, c), possibleValuesAt board r c) | r <- [0..n board - 1], c <- [0..n board - 1], board !! r !! c == 0]

-- Update possible values when placing a value
updatePossibleValues :: Board -> PossibleValues -> Int -> Int -> Int -> PossibleValues
updatePossibleValues board pv row col val = foldl updateCell pv affectedCells
  where
    n' = n board
    subSize = subGridSize board
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

-- Place a value in a cell and update possible values
updateBoard :: Board -> Int -> Int -> Int -> Board
updateBoard board row col val =
  [ [ if r == row && c == col then val else board !! r !! c
    | c <- [0..n board - 1] ]
  | r <- [0..n board - 1] ]

placeValue :: Board -> PossibleValues -> Int -> Int -> Int -> (Board, PossibleValues)
placeValue board pv row col val =
  let board' = updateBoard board row col val
      pv' = Map.delete (row, col) pv
      pv'' = updatePossibleValues board' pv' row col val
  in (board', pv'')

-- Select MRV cell
selectMRVCell :: PossibleValues -> Maybe (Int, Int)
selectMRVCell pv
  | Map.null pv = Nothing
  | otherwise = Just $ fst $ minimumBy (comparing (length . snd)) (Map.toList pv)

-- Order values using LCV
orderValues :: Board -> PossibleValues -> Int -> Int -> [Int]
orderValues board pv row col =
  let values = fromJust $ Map.lookup (row, col) pv
  in sortBy (comparing (constraintCount board pv row col)) values

constraintCount :: Board -> PossibleValues -> Int -> Int -> Int -> Int
constraintCount board pv row col val =
  let (board', pvAfter) = placeValue board pv row col val
      affectedCells = Map.keys pvAfter
  in sum [length $ fromMaybe [] (Map.lookup (r, c) pvAfter) | (r, c) <- affectedCells]

-- Print the board
printBoard :: Board -> IO ()
printBoard board = do
    mapM_ (putStrLn . unwords . map show) board
    putStrLn "----------------------------------------"

-- Check if the board is solved
isSolved :: Board -> Bool
isSolved = all (notElem 0)

-- Check if a list has unique values ignoring zeros
isUnique :: [Int] -> Bool
isUnique xs = let nonZeroValues = filter (/= 0) xs in length nonZeroValues == length (nub nonZeroValues)


-- Check if all rows, columns, and subgrids are valid
isValidSolution :: Board -> Bool
isValidSolution board =
    all isUnique [getRow board r | r <- [0..n board - 1]] &&
    all isUnique [getCol board c | c <- [0..n board - 1]] &&
    all isUnique [getSubGrid board r c | r <- [0, subGridSize board .. n board - 1], c <- [0, subGridSize board .. n board - 1]]


-- Solve Sudoku with optimizations, applying AC-3 only to MRV and its neighbors
solveSudoku :: Board -> PossibleValues -> IO (Maybe Board)
solveSudoku board pv
  | isSolved board = do
      printBoard board
      return (Just board)
  | otherwise = case selectMRVCell pv of
      Nothing -> return Nothing
      Just (row, col) -> do
          let orderedValues = orderValues board pv row col
          msum <$> mapM (tryValue row col) orderedValues
  where
    tryValue :: Int -> Int -> Int -> IO (Maybe Board)
    tryValue row col val = do
      let (board', pv') = placeValue board pv row col val
          neighbors' = neighbors board row col -- Find neighbors of the selected MRV cell
          reducedArcs = Set.fromList [((xi, xj), (xk, xl)) | (xi, xj) <- (row, col) : neighbors', (xk, xl) <- neighbors' ]
      case ac3 board' pv' reducedArcs of
        Nothing -> return Nothing  -- Inconsistency found, backtrack
        Just pv'' ->
          if any null (Map.elems pv'') then
            return Nothing  -- Dead end
          else
            solveSudoku board' pv''

-- AC-3 Algorithm for arc consistency, applied only to a subset of arcs (reduced scope)
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




-- Count the number of solutions with a limit on maximum solutions
countSolutions :: Board -> PossibleValues -> Int -> Int -> IO Int
countSolutions board pv acc maxSolutions
  | acc >= maxSolutions = return acc  -- Stop early if maxSolutions found
  | isSolved board && isValidSolution board = return (acc + 1)
  | otherwise = case selectMRVCell pv of
      Nothing -> return acc
      Just (row, col) -> do
          let orderedValues = orderValues board pv row col
          foldM tryValue acc orderedValues
        where
          tryValue acc' val
            | acc' >= maxSolutions = return acc'  -- Early exit
            | otherwise = do
                let (board', pv') = placeValue board pv row col val
                if any null (Map.elems pv') then
                  return acc'  -- Dead end
                else
                  countSolutions board' pv' acc' maxSolutions

-- Timing function
timeIt :: IO a -> IO (a, Double)
timeIt action = do
    start <- getCPUTime
    result <- action
    end <- getCPUTime
    let diff = fromIntegral (end - start) / (10^12)  -- Convert to seconds
    return (result, diff)

-- numSolutions function with a limit on the number of solutions
numSolutions :: Board -> IO Int
numSolutions board = do
    let pv = initializePossibleValues board
        maxSolutions = 2  -- Limit the number of solutions to 3
    (solutionCount, timeTaken) <- timeIt $ countSolutions board pv 0 maxSolutions
    putStrLn $ "Number of solutions: " ++ show solutionCount
    putStrLn $ "Time taken: " ++ show timeTaken ++ " seconds."
    return solutionCount
