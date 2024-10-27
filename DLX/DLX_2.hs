-- \/\/\/ DO NOT MODIFY THE FOLLOWING LINES \/\/\/
module SudokuSolver(Board, Solutions(..), author, nickname, numSolutions) where
import Sudoku(Board, Solutions(..))
-- /\/\/\ DO NOT MODIFY THE PRECEDING LINES /\/\/\


import Control.Monad.ST
import Data.STRef
import Control.Monad (forM_, when, replicateM)
import Data.Array.ST (STArray, newArray, readArray, writeArray)
import Data.Array.IArray (listArray)
import Data.Array.Unboxed (UArray, (!))
import Data.List
import Data.Ord (comparing)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map

-- import Debug.Trace (trace) -- Uncomment for debugging

author :: String
author = "Aoping Lyu"

nickname :: String
nickname = "SudokuOuSama-DLX"


{- DNode s
   Represents a node in the Dancing Links data structure for the DLX algorithm.
   Each node has pointers to its left, right, up, down neighbors, and a control node.
   The 'nodeSize' represents the size of the column for column headers.
   INVARIANT: The node connections (left, right, up, down) form a valid toroidal doubly linked list.
-}
data DNode s = DNode {left, right, up, down, control :: STRef s (DNode s),
                      nodeSize :: STRef s Int,
                      rowIdx, colIdx :: Int} | Null

instance Eq (DNode s) where
    a == b = rowIdx a == rowIdx b && colIdx a == colIdx b

newDNode l r u d size row col = do
    leftRef    <- newSTRef l
    rightRef   <- newSTRef r
    upRef      <- newSTRef u
    downRef    <- newSTRef d
    controlRef <- newSTRef Null
    sizeRef    <- newSTRef size
    return (DNode leftRef rightRef upRef downRef controlRef sizeRef row col)

getAttr :: (DNode s -> STRef s a) -> DNode s -> ST s a
getAttr dir node = readSTRef (dir node)

setAttr :: (DNode s -> STRef s a) -> DNode s -> a -> ST s ()
setAttr dir node = writeSTRef (dir node)

{- unlink prev next node
   Unlinks 'node' from its neighbors in one direction (defined by 'prev' and 'next').
-}
unlink :: (a -> STRef s a) -> (a -> STRef s a) -> a -> ST s ()
unlink prev next node = do
    before <- readSTRef (prev node)
    after  <- readSTRef (next node)
    writeSTRef (next before) after
    writeSTRef (prev after) before

{- relink prev next node
   Relinks 'node' into its neighbors in one direction (defined by 'prev' and 'next').
-}
relink :: (a -> STRef s a) -> (a -> STRef s a) -> a -> ST s ()
relink prev next node = do
    before <- readSTRef (prev node)
    after  <- readSTRef (next node)
    writeSTRef (next before) node
    writeSTRef (prev after) node

{- link prev next a b
   Links node 'a' to node 'b' in one direction (defined by 'prev' and 'next').
-}
link :: (DNode s -> STRef s (DNode s)) -> (DNode s -> STRef s (DNode s)) -> DNode s -> DNode s -> ST s ()
link prev next a b = do
    writeSTRef (next a) b
    writeSTRef (prev b) a

{- buildDLX bitmap nrow ncol
   Builds the Dancing Links (DLX) data structure from the given bitmap.
   RETURNS: The root header node of the DLX data structure.
-}
buildDLX :: [UArray Int Bool] -> Int -> Int -> ST s (DNode s)
buildDLX bitmap nrow ncol = do
    colHeaders <- newArray (0, ncol - 1) Null :: ST s (STArray s Int (DNode s))
    rootHeader <- newDNode Null Null Null Null 0 (-1) (-1)

    link left right rootHeader rootHeader

    forM_ [0 .. ncol - 1] $ \j -> do
        headerLeft <- getAttr left rootHeader
        colNode <- newDNode headerLeft rootHeader Null Null 0 (-1) j
        setAttr right headerLeft colNode
        setAttr left rootHeader colNode
        link up down colNode colNode
        writeArray colHeaders j colNode

    rowHeader <- newDNode Null Null Null Null 0 0 (-1)
    forM_ (zip [0 .. nrow - 1] bitmap) $ \(i, row) -> do
        setAttr left rowHeader rowHeader
        setAttr right rowHeader rowHeader

        forM_ [0 .. ncol - 1] $ \j -> do
            if row ! j then do

                colNode <- readArray colHeaders j
                leftNode <- getAttr left rowHeader
                upperNode <- getAttr up colNode

                -- Increment column size
                modifySTRef (nodeSize colNode) (+1)

                newRowNode <- newDNode leftNode rowHeader upperNode colNode 0 i j
                setAttr right leftNode newRowNode
                setAttr left rowHeader newRowNode
                setAttr down upperNode newRowNode
                setAttr up colNode newRowNode
                setAttr control newRowNode colNode
            else return ()

        leftNode <- getAttr left rowHeader
        rightNode <- getAttr right rowHeader
        setAttr right leftNode rightNode
        setAttr left rightNode leftNode

    return rootHeader

{- forEach step start f
   Iterates over the nodes in one direction starting from 'start', applying function 'f' to each node.
   The direction is determined by the 'step' function.
-}
forEach :: (DNode s -> ST s (DNode s)) -> DNode s -> (DNode s -> ST s ()) -> ST s ()
forEach step start f = step start >>= loop
  where
    loop current = when (current /= start) (f current >> step current >>= loop)

{- setCover controlNode
   Covers a column in the DLX data structure, removing it and its rows from the matrix.
-}
setCover :: DNode s -> ST s ()
setCover controlNode = do
    -- Unlink the controlNode (column header) from the row
    unlink left right controlNode

    -- Unlink each node in the column and decrement the size count
    forEach (getAttr down) controlNode $ \node ->
        forEach (getAttr right) node $ \neighbor -> do
            unlink up down neighbor
            colNode <- getAttr control neighbor
            currentSize <- getAttr nodeSize colNode
            setAttr nodeSize colNode (currentSize - 1)

{- setUncover controlNode
   Uncovers a column in the DLX data structure, restoring it and its rows to the matrix.
-}

setUncover :: DNode s -> ST s ()
setUncover controlNode = do
    -- Relink each node in the column and increment the size count
    forEach (getAttr up) controlNode $ \node ->
        forEach (getAttr left) node $ \neighbor -> do
            colNode <- getAttr control neighbor
            currentSize <- getAttr nodeSize colNode
            setAttr nodeSize colNode (currentSize + 1)
            relink up down neighbor

    -- Relink the controlNode (column header) into the row
    relink left right controlNode


{- solve bitmap numCols
   Solves the exact cover problem using the DLX algorithm for the given bitmap.
   RETURNS: A list of solutions, where each solution is a list of row indices.
-}
solve :: [UArray Int Bool] -> Int -> [[Int]]
solve bitmap numCols = 
    runST $ do
        dlx <- buildDLX bitmap (length bitmap) numCols
        solutions <- newSTRef []
        solutionCount <- newSTRef 0
        search dlx solutions solutionCount []
        readSTRef solutions
  where
    search rootHeader solutions countRef plan = do
        leftmost <- getAttr right rootHeader
        if leftmost == rootHeader 
        then do
            modifySTRef solutions (plan :)
            modifySTRef countRef (+1)
            count <- readSTRef countRef
            when (count >= 2) $ return ()  -- Stop search if we have 2 solutions
        else do
            -- Choose the column with the minimum number of nodes
            (minColSize, selectedCol) <- selectBest rootHeader
            setCover selectedCol

            -- Try each row in the selected column
            forEach (getAttr down) selectedCol $ \row -> do
                coverRow row
                solutionCount <- readSTRef countRef
                when (solutionCount < 2) $ search rootHeader solutions countRef (rowIdx row : plan)
                uncoverRow row

            setUncover selectedCol

    {- selectBest headNode
       Selects the column with the minimum node size for heuristic optimization.
       RETURNS: A tuple of (column size, column node).
    -}
    selectBest headNode = do
        minCol <- newSTRef (maxBound :: Int, Null)
        forEach (getAttr right) headNode $ \col -> do
            colSize <- getAttr nodeSize col
            (minSize, _) <- readSTRef minCol
            when (colSize < minSize) $ writeSTRef minCol (colSize, col)
        readSTRef minCol

    {- coverRow row
       Covers all columns related to the given row.
    -}
    coverRow row = forEach (getAttr right) row $ \node -> do
        controlCol <- getAttr control node
        setCover controlCol

    {- uncoverRow row
       Uncovers all columns related to the given row.
    -}
    uncoverRow row = forEach (getAttr left) row $ \node -> do
        controlCol <- getAttr control node
        setUncover controlCol

{- makeBits positions n
   Creates a bit vector of length 'n' with 'True' at indices specified in 'positions' and 'False' elsewhere.
   RETURNS: A list of Bool representing the bit vector.
   EXAMPLES: makeBits [1,3] 5 = [False, True, False, True, False]
-}
makeBits :: [Int] -> Int -> [Bool]
makeBits [] n = replicate n False
makeBits (x:xs) n = replicate x False ++ True : makeBits (map (\t -> t - x - 1) xs) (n - x - 1)

{- generateBitmap blockN sudokuN secN colN allRows
   Generates the bitmap for the exact cover problem representing the Sudoku constraints.
   RETURNS: A list of UArray Int Bool representing the bitmap rows.
-}
generateBitmap :: Int -> Int -> Int -> Int -> [(Int, Int, Int)] -> [UArray Int Bool]
generateBitmap blockN sudokuN secN colN allRows =
    [ listArray (0, colN - 1) $ 
        makeBits [ x * blockN + y,                            -- Cell constraint
                   secN + ((x `div` sudokuN) * sudokuN + y `div` sudokuN) * blockN + d - 1, -- Block constraint
                   secN * 2 + x * blockN + d - 1,             -- Row constraint
                   secN * 3 + y * blockN + d - 1 ] colN       -- Column constraint
    | (x, y, d) <- allRows ]

{- existingNumbersRow board x
   Retrieves existing numbers in row 'x' of the board.
   RETURNS: A list of Int representing the numbers present in row 'x'.
-}
existingNumbersRow :: Board -> Int -> [Int]
existingNumbersRow board x = filter (/= 0) $ board !! x

{- existingNumbersCol board y
   Retrieves existing numbers in column 'y' of the board.
   RETURNS: A list of Int representing the numbers present in column 'y'.
-}
existingNumbersCol :: Board -> Int -> [Int]
existingNumbersCol board y = filter (/= 0) $ map (!! y) board

{- existingNumbersBlock board x y
   Retrieves existing numbers in the block containing cell (x, y).
   RETURNS: A list of Int representing the numbers present in the block.
-}
existingNumbersBlock :: Board -> Int -> Int -> [Int]
existingNumbersBlock board x y = filter (/= 0) 
    [ board !! i !! j | i <- [blockStartX..blockStartX+blockSize-1],
                        j <- [blockStartY..blockStartY+blockSize-1]]
  where
    blockSize = floor (sqrt (fromIntegral $ length board))
    blockStartX = (x `div` blockSize) * blockSize
    blockStartY = (y `div` blockSize) * blockSize

{- initialCandidates board
   Generates initial candidates for each cell in the Sudoku board.
   RETURNS: A Map from (Int, Int) positions to lists of possible candidate numbers.
-}
initialCandidates :: Board -> Map.Map (Int, Int) [Int]
initialCandidates board = Map.fromList
    [ ((x, y), candidates)
    | x <- [0..blockN - 1], y <- [0..blockN - 1],
      let cellValue = board !! x !! y,
      let candidates = if cellValue == 0 
                       then [1..blockN] \\ (existingNumbersRow board x ++ existingNumbersCol board y ++ existingNumbersBlock board x y)
                       else [cellValue]
    ]
  where
    blockN = length board

{- combinations n xs
   Generates all combinations of size 'n' from the list 'xs'.
   RETURNS: A list of combinations, each being a list of 'n' elements.
   EXAMPLES: combinations 2 [1,2,3] = [[1,2],[1,3],[2,3]]
-}
combinations :: Int -> [a] -> [[a]]
combinations 0 _  = [[]]
combinations _ [] = []
combinations n (x:xs) = [ x:ys | ys <- combinations (n-1) xs ] ++ combinations n xs

{- units size sudokuN
   Generates all units (rows, columns, blocks) for a Sudoku board.
   RETURNS: A list of units, each unit being a list of (Int, Int) positions.
-}
units :: Int -> Int -> [[(Int, Int)]]
units size sudokuN = rows ++ cols ++ blocks
  where
    rows = [[ (x, y) | y <- [0..size - 1]] | x <- [0..size - 1]]
    cols = [[ (x, y) | x <- [0..size - 1]] | y <- [0..size - 1]]
    blocks = [ [ (x, y) | x <- [bx * sudokuN .. (bx + 1) * sudokuN - 1],
                          y <- [by * sudokuN .. (by + 1) * sudokuN - 1] ]
             | bx <- [0..sudokuN - 1], by <- [0..sudokuN - 1]]

{- applyNakedSubsets ns candidates
   Applies naked subsets strategy for subset sizes in 'ns' to refine candidates.
   RETURNS: Updated candidates after applying naked subsets.
-}
applyNakedSubsets :: [Int] -> Map.Map (Int, Int) [Int] -> Map.Map (Int, Int) [Int]
applyNakedSubsets ns candidates = foldl (\cand n -> foldl (applyNakedSubsetsUnit n) cand unitsList) candidates ns
  where
    size = maximum (concatMap (\(x, y) -> [x, y]) (Map.keys candidates)) + 1  -- Assuming square board
    sudokuN = floor (sqrt (fromIntegral size))
    unitsList = units size sudokuN

{- applyNakedSubsetsUnit n cand unit
   Applies naked subsets of size 'n' within a single unit to refine candidates.
   RETURNS: Updated candidates after applying naked subsets in the unit.
-}
applyNakedSubsetsUnit :: Int -> Map.Map (Int, Int) [Int] -> [(Int, Int)] -> Map.Map (Int, Int) [Int]
applyNakedSubsetsUnit n cand unit = foldl eliminateCandidates cand nakedSubsets
  where
    -- Find all cells with candidates of length between 2 and n
    possibleSubsets = [ (pos, cands) | pos <- unit,
                                       let cands = Map.findWithDefault [] pos cand,
                                       length cands >= 2, length cands <= n ]
    positionCandidates = Map.fromList possibleSubsets
    -- Generate combinations of positions of size n
    positionCombinations = combinations n (map fst possibleSubsets)
    nakedSubsets = [ (combinedCands, positions) |
                     positions <- positionCombinations,
                     let combinedCands = nub (concatMap (\pos -> Map.findWithDefault [] pos cand) positions),
                     length combinedCands == n,
                     all (\pos -> let cands = Map.findWithDefault [] pos cand in all (`elem` combinedCands) cands) positions ]
    -- Eliminate naked subset candidates from other cells
    eliminateCandidates cand (subsetCands, subsetPositions) = foldl eliminateFromCell cand otherPositions
      where
        otherPositions = unit \\ subsetPositions
        eliminateFromCell c pos = Map.adjust (\cs -> cs \\ subsetCands) pos c

{- applyHiddenSubsets ns candidates
   Applies hidden subsets strategy for subset sizes in 'ns' to refine candidates.
   RETURNS: Updated candidates after applying hidden subsets.
-}
applyHiddenSubsets :: [Int] -> Map.Map (Int, Int) [Int] -> Map.Map (Int, Int) [Int]
applyHiddenSubsets ns candidates = foldl (\cand n -> foldl (applyHiddenSubsetsUnit n) cand unitsList) candidates ns
  where
    size = maximum (concatMap (\(x, y) -> [x, y]) (Map.keys candidates)) + 1  -- Assuming square board
    sudokuN = floor (sqrt (fromIntegral size))
    unitsList = units size sudokuN

{- applyHiddenSubsetsUnit n cand unit
   Applies hidden subsets of size 'n' within a single unit to refine candidates.
   RETURNS: Updated candidates after applying hidden subsets in the unit.
-}
applyHiddenSubsetsUnit :: Int -> Map.Map (Int, Int) [Int] -> [(Int, Int)] -> Map.Map (Int, Int) [Int]
applyHiddenSubsetsUnit n cand unit = foldl eliminateCandidates cand hiddenSubsets
  where
    -- Count occurrences of each candidate
    candidateCounts = Map.fromListWith (++) [ (num, [pos]) | pos <- unit, num <- Map.findWithDefault [] pos cand ]
    -- Candidates that appear in 2 to n positions
    candidatesWithOccurrences = [ (num, positions) | (num, positions) <- Map.toList candidateCounts, length positions >= 2, length positions <= n ]
    -- Generate combinations of candidates of size n
    candidateCombinations = combinations n (map fst candidatesWithOccurrences)
    hiddenSubsets = [ (subsetCands, positions) |
                      subsetCands <- candidateCombinations,
                      let positions = foldl1 intersect [ Map.findWithDefault [] num candidateCounts | num <- subsetCands ],
                      length positions == n ]
    -- Eliminate other candidates from these positions
    eliminateCandidates cand (subsetCands, subsetPositions) = foldl eliminateFromCell cand subsetPositions
      where
        eliminateFromCell c pos = Map.adjust (\cs -> cs `intersect` subsetCands) pos c


{- refineCandidates candidates
   Repeatedly applies strategies to refine the candidates until no changes occur.
   RETURNS: Final refined candidates.
-}
refineCandidates :: Map.Map (Int, Int) [Int] -> Map.Map (Int, Int) [Int]
refineCandidates candidates =
    let newCandidates = applyHiddenSubsets [2, 3] $ applyNakedSubsets [2, 3] candidates
    in if newCandidates == candidates
       then candidates
       else refineCandidates newCandidates

{- sudoku prob
   Solves the given Sudoku problem.
   RETURNS: A tuple containing a list of solution boards and the solution status.
   EXAMPLES: sudoku initialBoard = ([solutionBoard], UniqueSolution)
-}
sudoku :: Board -> ([Board], Solutions)
sudoku prob = 
    let initialCand = initialCandidates prob
        refinedCand = refineCandidates initialCand
        -- Now generate all possible (x, y, d) based on refined candidates
        allPositions = Map.keys refinedCand
        fixed = [ (x, y, head ds) | ((x, y), ds) <- Map.toList refinedCand, length ds == 1 ]
        candidates = [ (x, y, d) | ((x, y), ds) <- Map.toList refinedCand, length ds > 1, d <- ds ]
        -- allRows = trace ("Total rows generated: " ++ show (length fixed + length candidates))
        --           (fixed ++ candidates)
        allRows = fixed ++ candidates
        blockN = length prob
        sudokuN = floor (sqrt (fromIntegral blockN))
        secN = blockN ^ 2
        colN = secN * 4
        bitmap = generateBitmap blockN sudokuN secN colN allRows
        solutions = solve bitmap colN
        boardSolutions = map (\sol -> buildBoard sol allRows blockN) solutions
    in case length boardSolutions of
        0 -> ([], NoSolution)
        1 -> (boardSolutions, UniqueSolution)
        _ -> (boardSolutions, MultipleSolutions)
    where
        {- buildBoard sol allRows blockN
       Constructs a Sudoku board from the solution indices and possible moves.
       RETURNS: A completed Sudoku board.
        -}
        buildBoard sol allRows blockN = 
            let posMap = Map.fromList [ (idx, (x, y, d)) | (idx, (x, y, d)) <- zip [0..] allRows ]
                boardList = [ [ cellValue x y | y <- [0..blockN -1] ] | x <- [0..blockN -1] ]
                cellValue x y = let maybeEntry = find (\(idx, (i, j, _)) -> i == x && j == y && idx `elem` sol) (Map.toList posMap)
                                in case maybeEntry of
                                    Just (_, (_, _, d)) -> d
                                    Nothing -> 0
            in boardList

{- numSolutions board
   Determines the number of solutions for the given Sudoku board.
   RETURNS: Solutions status (NoSolution, UniqueSolution, MultipleSolutions).
-}
numSolutions :: Board -> Solutions
numSolutions board =
    let (_, sol) = sudoku board
    in sol


{- Uncomment the following code to run the Sudoku solver with ghci

-- Show instance for Solutions
instance Show Solutions where
    show NoSolution = "NoSolution"
    show UniqueSolution = "UniqueSolution"
    show MultipleSolutions = "MultipleSolutions"

-- Play Sudoku with a predefined or manually entered board
solveSudoku :: Board -> IO ()
solveSudoku board = do
    let (solutions, solutionType) = sudoku board
    putStrLn $ "Solution type: " ++ show solutionType
    mapM_ printBoard solutions

-- Board printing function
printBoard :: Board -> IO ()
printBoard board = do
    mapM_ (putStrLn . unwords . map show) board
    putStrLn "----------------------------------------"
-}