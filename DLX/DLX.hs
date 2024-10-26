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

import Debug.Trace (trace)


author :: String
author = "Aoping Lyu"  -- replace `undefined' with your first and last name

nickname :: String
nickname = "SudokuOuSama" -- replace `undefined' with a nickname for your solver


data DNode s = DNode {left, right, up, down, ctl :: STRef s (DNode s),
                      size :: STRef s Int,
                      row, col :: Int} | Null

instance Eq (DNode s) where
    a == b = row a == row b && col a == col b

newDNode l r u d size row col =
        do l' <- newSTRef l
           r' <- newSTRef r
           u' <- newSTRef u
           d' <- newSTRef d
           ctl' <- newSTRef Null
           size' <- newSTRef size
           return (DNode l' r' u' d' ctl' size' row col)

getAttr :: (DNode s -> STRef s a) -> DNode s -> ST s a
getAttr dir node = readSTRef (dir node)

setAttr :: (DNode s -> STRef s a) -> DNode s -> a -> ST s ()
setAttr dir node = writeSTRef (dir node)

buildDLX :: [UArray Int Bool] -> Int -> Int -> ST s (DNode s)
buildDLX bitmap nrow ncol =
    do chead <- newArray (0, ncol - 1) Null :: ST s (STArray s Int (DNode s))
       h <- newDNode Null Null Null Null 0 (-1) (-1)
       setAttr left h h
       setAttr right h h
       setAttr up h h
       setAttr down h h
       forM_ [0..ncol-1] $ \j -> do
           hl <- getAttr left h
           p <- newDNode hl h Null Null 0 (-1) j
           setAttr right hl p
           setAttr left h p
           setAttr up p p
           setAttr down p p
           writeArray chead j p
       rhead <- newDNode Null Null Null Null 0 0 (-1)
       forM_ (zip [0..nrow-1] bitmap) $ \(i, row) -> do
           setAttr left rhead rhead
           setAttr right rhead rhead
           forM_ [0..ncol-1] $ \j -> do
               if row ! j then do
                    rl <- getAttr left rhead
                    ct <- readArray chead j
                    cs <- getAttr size ct
                    setAttr size ct (cs + 1)
                    cu <- getAttr up ct
                    p <- newDNode rl rhead cu ct 0 i j
                    setAttr right rl p
                    setAttr left rhead p
                    setAttr down cu p
                    setAttr up ct p
                    setAttr ctl p ct
               else return ()
           rl <- getAttr left rhead
           rr <- getAttr right rhead
           setAttr right rl rr
           setAttr left rr rl
       return h

forEach step start f = step start >>= loop
    where loop now = when (now /= start) (f now >> step now >>= loop)

setCover :: DNode s -> ST s ()
setCover pctl =
        do cl <- getAttr left pctl
           cr <- getAttr right pctl
           setAttr right cl cr
           setAttr left cr cl
           forEach (getAttr down) pctl $ \p ->
             forEach (getAttr right) p $ \q -> do
                 qu <- getAttr up q
                 qd <- getAttr down q
                 qct <- getAttr ctl q
                 qcs <- getAttr size qct
                 setAttr down qu qd
                 setAttr up qd qu
                 setAttr size qct (qcs - 1)

setUncover :: DNode s -> ST s ()
setUncover pctl =
        do cl <- getAttr left pctl
           cr <- getAttr right pctl
           setAttr right cl pctl
           setAttr left cr pctl
           forEach (getAttr up) pctl $ \p ->
             forEach (getAttr left) p $ \q -> do
                 qu <- getAttr up q
                 qd <- getAttr down q
                 qct <- getAttr ctl q
                 qcs <- getAttr size qct
                 setAttr down qu q
                 setAttr up qd q
                 setAttr size qct (qcs + 1)

solve bitmap ncol = 
    runST $ do
        dlx <- buildDLX bitmap (length bitmap) ncol
        solutionsRef <- newSTRef []
        countRef <- newSTRef 0
        solve' dlx solutionsRef countRef 0 []
        readSTRef solutionsRef
    where
        solve' head solutionsRef countRef step plan = do
            hl <- getAttr left head
            if hl == head then do
                -- Found a solution
                modifySTRef solutionsRef (plan:)
                modifySTRef countRef (+1)
                count <- readSTRef countRef
                if count >= 2 then
                    return ()  -- Stop recursion
                else
                    return ()
            else do
                -- Continue searching
                best <- newSTRef (9999, Null)
                forEach (getAttr right) head $ \p -> do
                    sp <- getAttr size p
                    (m, y) <- readSTRef best
                    when (sp < m)
                        (writeSTRef best (sp, p))
                (_, y) <- readSTRef best
                setCover y
                forEach (getAttr down) y $ \p -> do
                    forEach (getAttr right) p $ \q -> do
                        qctl <- getAttr ctl q
                        setCover qctl
                    count <- readSTRef countRef
                    when (count < 2) $ do
                        solve' head solutionsRef countRef (step + 1) (row p:plan)
                    forEach (getAttr left) p $ \q -> do
                        qctl <- getAttr ctl q
                        setUncover qctl
                setUncover y

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
        fixed = filter (\(_, _, d) -> d /= 0) $
                    concatMap (\(r, l) -> zipWith (\c x -> (r, c, x)) [0..] l) (zip [0..] prob)
        fixedPos = map (\(a, b, _) -> (a, b)) fixed
        -- allRows = fixed ++ [(x, y, d) | x <- [0..blockN - 1], y <- [0..blockN - 1],
        --                                 d <- [1..blockN], (x, y) `notElem` fixedPos]
        allRows = trace ("Total rows generated: " ++ show (length (fixed ++ [(x, y, d) | x <- [0..blockN - 1], 
                                                                        y <- [0..blockN - 1], 
                                                                        d <- [1..blockN], 
                                                                        (x, y) `notElem` fixedPos])))
            (fixed ++ [(x, y, d) | x <- [0..blockN - 1], y <- [0..blockN - 1],
                                    d <- [1..blockN], (x, y) `notElem` fixedPos])
        makeBits [] n = replicate n False
        makeBits (x:xs) n = replicate x False ++ (True:makeBits (map (\t -> t - x - 1) xs) (n - x - 1))
        bitmap = [listArray (0, colN - 1) $
                    makeBits [x * blockN + y,
                              secN + ((x `div` sudokuN) * sudokuN + y `div` sudokuN) * blockN + d - 1,
                              secN * 2 + x * blockN + d - 1,
                              secN * 3 + y * blockN + d - 1] colN | (x, y, d) <- allRows]


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
