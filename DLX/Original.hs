import Data.STRef.Lazy
import Data.Array.ST (STArray, newArray, readArray, writeArray)
import Data.Array.IArray (listArray)
import Data.Array.Unboxed (UArray, (!))
import Control.Monad.ST.Lazy
import Control.Monad (replicateM, forM_, when)
import Data.List
--import System.IO.Unsafe (unsafePerformIO)

data DNode s = DNode {left, right, up, down, ctl :: STRef s (DNode s),
                      size :: STRef s Int,
                      row, col :: Int} | Null

instance Eq (DNode s) where
    --Null == Null = True
    --Null == (DNode _ _ _ _ _ _ _ _) = False
    --(DNode _ _ _ _ _ _ _ _) == Null = False
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

forEach' step start f = step start >>= loop
    where loop now = if now /= start then do
                            r <- f now
                            rs <- step now >>= loop
                            return (r:rs)
                     else return []

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
    runST $ do dlx <- buildDLX bitmap (length bitmap) ncol
               solve' dlx 0 []
    where solve' head step plan =
            do hl <- getAttr left head
               if hl == head then
                   return [plan]
               else do
                   best <- newSTRef (9999, Null)
                   forEach (getAttr right) head $ \p -> do
                       sp <- getAttr size p
                       (m, y) <- readSTRef best
                       when (sp < m)
                           (writeSTRef best (sp, p))
                   (m, y) <- readSTRef best
                   --y <- getAttr right head
                   setCover y
                   res <-
                     forEach' (getAttr down) y $ \p -> do
                         forEach (getAttr right) p $ \q -> do
                             qctl <- getAttr ctl q
                             setCover qctl
                         r' <- solve' head (step + 1) (row p:plan)
                         forEach (getAttr left) p $ \q -> do
                             qctl <- getAttr ctl q
                             setUncover qctl
                         return r'
                   setUncover y
                   return (concat res)

sudoku :: [[Int]] -> [[[Int]]]
sudoku prob = [[[d | y <- [0..blockN - 1],
                     d <- [1..blockN],
                     (x, y, d) `elem` pos] |
                        x <- [0..blockN - 1],
                        let pos = map (\x -> all!!x) sol] | sol <- solve bitmap colN]
    where sudokuN = 3
          blockN = sudokuN ^ 2
          secN = blockN ^ 2
          colN = secN * 4
          fixed = filter (\(_, _, d) -> d /= 0) $
                    concatMap (\(r, l) -> (zipWith (\c x -> (r, c, x)) [0..]) l) (zip [0..] prob)
          fixedPos = map (\(a, b, _) -> (a, b)) fixed
          all = fixed ++ [(x, y, d) | x <- [0..blockN - 1], y <- [0..blockN - 1],
                                      d <- [1..blockN], (x, y) `notElem` fixedPos]
          makeBits [] n = replicate n False
          makeBits (x:xs) n = replicate x False ++ (True:makeBits (map (\t -> t - x - 1) xs) (n - x - 1))
          bitmap = [listArray (0, colN - 1) $
                        makeBits [x * blockN + y,
                                  secN + ((x `div` sudokuN) * sudokuN + y `div` sudokuN) * blockN + d - 1,
                                  secN * 2 + x * blockN + d - 1,
                                  secN * 3 + y * blockN + d - 1] colN | (x, y, d) <- all]

split _ [] = []
split c s
    | s' == [] = []
    | otherwise = let (h, rest) = span (/= c) s' in h:split c rest
    where s' = snd $ span (== c) s

main = do lines <- replicateM 9 getLine
          let prob = map (\l -> map read (split ' ' l) :: [Int]) lines
          forM_ (sudoku prob) $ \sol -> do
              putStrLn $ intercalate "\n" (map (\l -> intercalate " " (map show l)) sol) ++ "\n"