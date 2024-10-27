-- \/\/\/ DO NOT MODIFY THE FOLLOWING LINES \/\/\/
module SudokuSolver(Board, Solutions(..), author, nickname, numSolutions) where
import Sudoku(Board, Solutions(..))


-- /\/\/\ DO NOT MODIFY THE PRECEDING LINES /\/\/\

import TestCases (board0, board1, board2, board3, board4, board5, board6, board7, board10)

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

import Control.Monad.ST
import Data.STRef
import Control.Monad (forM_, when, replicateM)
import Data.Array.ST (STArray, newArray, readArray, writeArray)
import Data.Array.IArray (listArray)
import Data.Array.Unboxed (UArray, (!))
import Data.List
import Data.List (maximumBy)
import Data.Ord (comparing)
import qualified Data.Set as Set
import Debug.Trace (trace)


author :: String
author = "Aoping Lyu"  -- replace `undefined' with your first and last name

nickname :: String
nickname = "SudokuOuSama-DLX" -- replace `undefined' with a nickname for your solver


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

-- Unlink and link functions for removing and restoring nodes
unlink :: (a -> STRef s a) -> (a -> STRef s a) -> a -> ST s ()
unlink prev next node = do
    before <- readSTRef (prev node)
    after  <- readSTRef (next node)
    writeSTRef (next before) after
    writeSTRef (prev after) before

relink :: (a -> STRef s a) -> (a -> STRef s a) -> a -> ST s ()
relink prev next node = do
    before <- readSTRef (prev node)
    after  <- readSTRef (next node)
    writeSTRef (next before) node
    writeSTRef (prev after) node

link :: (DNode s -> STRef s (DNode s)) -> (DNode s -> STRef s (DNode s)) -> DNode s -> DNode s -> ST s ()
link prev next a b = do
    writeSTRef (next a) b
    writeSTRef (prev b) a


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



forEach :: (DNode s -> ST s (DNode s)) -> DNode s -> (DNode s -> ST s ()) -> ST s ()
forEach step start f = step start >>= loop
  where
    loop current = when (current /= start) (f current >> step current >>= loop)


-- Updated setCover function using unlink
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

-- Updated setUncover function using relink
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
        leftmost <- getAttr left rootHeader
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

    selectBest headNode = do
        minCol <- newSTRef (maxBound :: Int, Null)
        forEach (getAttr right) headNode $ \col -> do
            colSize <- getAttr nodeSize col
            (minSize, _) <- readSTRef minCol
            when (colSize < minSize) $ writeSTRef minCol (colSize, col)
        readSTRef minCol

    coverRow row = forEach (getAttr right) row $ \node -> do
        controlCol <- getAttr control node
        setCover controlCol

    uncoverRow row = forEach (getAttr left) row $ \node -> do
        controlCol <- getAttr control node
        setUncover controlCol
   



existingNumbers :: Board -> Int -> Int -> [Int]
existingNumbers board x y = nub $ rowNums ++ colNums ++ blockNums
  where
    blockSize = floor . sqrt . fromIntegral $ length board
    rowNums = board !! x
    colNums = map (!! y) board
    blockStartX = (x `div` blockSize) * blockSize
    blockStartY = (y `div` blockSize) * blockSize
    blockNums = [board !! i !! j | i <- [blockStartX..blockStartX+blockSize-1],
                                   j <- [blockStartY..blockStartY+blockSize-1]]


-- Helper function to create the bit vector
makeBits :: [Int] -> Int -> [Bool]
makeBits [] n = replicate n False
makeBits (x:xs) n = replicate x False ++ True : makeBits (map (\t -> t - x - 1) xs) (n - x - 1)

-- Generate bitmaps for all (x, y, d) constraints in allRows
generateBitmap :: Int -> Int -> Int -> Int -> [(Int, Int, Int)] -> [UArray Int Bool]
generateBitmap blockN sudokuN secN colN allRows =
    [ listArray (0, colN - 1) $ 
        makeBits [ x * blockN + y,                            -- Cell constraint
                   secN + ((x `div` sudokuN) * sudokuN + y `div` sudokuN) * blockN + d - 1, -- SubGrid constraint
                   secN * 2 + x * blockN + d - 1,             -- Row constraint
                   secN * 3 + y * blockN + d - 1 ] colN       -- Column constraint
    | (x, y, d) <- allRows ]

sudoku :: Board -> ([Board], Solutions)
sudoku prob = 
    let solutions = solve bitmap colN
        boardSolutions = map (\sol -> [[d | y <- [0..blockN - 1],
                                           d <- [1..blockN],
                                           (x, y, d) `elem` pos] |
                                            x <- [0..blockN - 1],
                                            let pos = map (\x -> allRows!!x) sol]) solutions
    in case length boardSolutions of
        0 -> ([], NoSolution)
        1 -> (boardSolutions, UniqueSolution)
        _ -> (boardSolutions, MultipleSolutions)
    where
        blockN = length prob
        sudokuN = floor . sqrt . fromIntegral $ blockN
        secN = blockN ^ 2
        colN = secN * 4
        fixed = [ (r, c, d) | (r, row) <- zip [0..] prob, (c, d) <- zip [0..] row, d /= 0 ]
        fixedPos = map (\(a, b, _) -> (a, b)) fixed

        -- 计算空白格子的候选数字表并输出已填入的数量
        candidates = trace ("Directly filled cells: " ++ show directlyFilledCount)
                      [ (x, y, d) | (x, y) <- [(i, j) | i <- [0..blockN - 1], j <- [0..blockN - 1]],
                        let ds = [1..blockN] \\ existingNumbers prob x y,
                        d <- ds, (x, y) `notElem` fixedPos ]
          where
            directlyFilledCount = length [ (x, y) | (x, y) <- [(i, j) | i <- [0..blockN - 1], j <- [0..blockN - 1]],
                                    let ds = [1..blockN] \\ existingNumbers prob x y,
                                    length ds == 1, (x, y) `notElem` fixedPos ]
        
        -- 生成可能的数字放置组合
        allRows = trace ("Total rows generated: " ++ show (length fixed + length candidates))
                  (fixed ++ candidates)
        bitmap = generateBitmap blockN sudokuN secN colN allRows



-- numSolutions function definition
numSolutions :: Board -> Solutions
numSolutions board =
    let (_, sol) = sudoku board
    in sol

-- Show instance for Solutions
instance Show Solutions where
    show NoSolution = "NoSolution"
    show UniqueSolution = "UniqueSolution"
    show MultipleSolutions = "MultipleSolutions"

-- Play Sudoku with a predefined or manually entered board
playSudoku :: Board -> IO ()
playSudoku board = do
    let (solutions, solutionType) = sudoku board
    putStrLn $ "Solution type: " ++ show solutionType
    mapM_ printBoard solutions

-- Board printing function
printBoard :: Board -> IO ()
printBoard board = do
    mapM_ (putStrLn . unwords . map show) board
    putStrLn "----------------------------------------"

