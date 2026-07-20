{-# LANGUAGE FlexibleContexts #-}
module Sift.Cdcl.Search
  ( solveInternal
  , luby
  , propagate
  , analyze
  , analyzeFinal
  , pickBranchVar
  , maybeReduce
  , installLearnt
  , extractModel
  , collectStats
  ) where

import Control.Monad (when, forM_, foldM, filterM)
import Control.Monad.ST (ST)
import Data.STRef
import Data.Array.ST
import qualified Data.IntSet as IntSet
import Sift.Cdcl.State
import Sift.Cdcl.Heap
import Sift.Stats

luby :: Int -> Int
luby x0 = descend size0 seq0 x0
  where
    (size0, seq0) = ascend 1 0
    ascend :: Int -> Int -> (Int, Int)
    ascend size sq
      | size < x0 + 1 = ascend (2 * size + 1) (sq + 1)
      | otherwise     = (size, sq)
    descend :: Int -> Int -> Int -> Int
    descend size sq x
      | size - 1 == x = 2 ^ sq
      | otherwise =
          let size' = (size - 1) `div` 2
          in descend size' (sq - 1) (x `mod` size')

propagate :: Solver s -> ST s Cid
propagate s = loop
  where
    loop = do
      qh <- readSTRef (qhead s)
      n  <- readSTRef (trailN s)
      if qh >= n
        then pure (-1)
        else do
          p <- readArray (trail s) qh
          writeSTRef (qhead s) (qh + 1)
          modifySTRef' (statProp s) (+ 1)
          confl <- propagateLit s p
          if confl >= 0 then pure confl else loop

propagateLit :: Solver s -> Int -> ST s Cid
propagateLit s p = do
  ws <- readArray (watches s) p
  writeArray (watches s) p []
  go ws []
  where
    falseLit = litNeg p
    go [] kept = do
      writeArray (watches s) p kept
      pure (-1)
    go (w@(Watcher cid blocker) : rest) kept = do
      bv <- litValueInt s blocker
      if bv == 1
        then go rest (w : kept)
        else do
          cl <- getClause s cid
          dead <- readSTRef (clsDead cl)
          if dead
            then go rest kept
            else do
              let lits = clsLits cl
                  sz = clsSize cl
              l0 <- readArray lits 0
              when (l0 == falseLit) $ do
                l1 <- readArray lits 1
                writeArray lits 0 l1
                writeArray lits 1 l0
              first <- readArray lits 0
              fv <- litValueInt s first
              if fv == 1
                then go rest (Watcher cid first : kept)
                else do
                  mNew <- findNewWatch s lits sz 2
                  case mNew of
                    Just k -> do
                      lk <- readArray lits k
                      writeArray lits 1 lk
                      writeArray lits k falseLit
                      modifyWatch s (litNeg lk) (Watcher cid first)
                      go rest kept
                    Nothing ->
                      if fv == -1
                        then do
                          writeArray (watches s) p (reverse kept ++ (w : rest))
                          pure cid
                        else do
                          _ <- enqueue s first cid
                          go rest (Watcher cid first : kept)

findNewWatch :: Solver s -> STUArray s Int Int -> Int -> Int -> ST s (Maybe Int)
findNewWatch s lits sz i
  | i >= sz = pure Nothing
  | otherwise = do
      l <- readArray lits i
      lv <- litValueInt s l
      if lv /= -1 then pure (Just i) else findNewWatch s lits sz (i + 1)

analyze :: Solver s -> Cid -> ST s ([Int], Int, Int)
analyze s conflict0 = do
  dl <- currentLevel s
  othersRef <- newSTRef []
  counterRef <- newSTRef (0 :: Int)
  pathRef <- newSTRef conflict0
  pivotRef <- newSTRef (-1 :: Int)
  idxRef <- newSTRef =<< (subtract 1 <$> readSTRef (trailN s))
  let step = do
        cid <- readSTRef pathRef
        cl <- getClause s cid
        when (clsLearnt cl) $ claBumpActivity s cl
        let lits = clsLits cl
            sz = clsSize cl
        pivot <- readSTRef pivotRef
        forM_ [0 .. sz - 1] $ \j -> do
          q <- readArray lits j
          when (q /= pivot) $ do
            let v = litVar q
            sv <- readArray (seen s) v
            lev <- readArray (varLevel s) v
            when (not sv && lev > 0) $ do
              varBumpActivity s v
              writeArray (seen s) v True
              if lev >= dl
                then modifySTRef' counterRef (+ 1)
                else modifySTRef' othersRef (q :)
        let selectNext = do
              i <- readSTRef idxRef
              l <- readArray (trail s) i
              sv <- readArray (seen s) (litVar l)
              if sv then pure (i, l) else do writeSTRef idxRef (i - 1); selectNext
        (i, l) <- selectNext
        writeSTRef idxRef (i - 1)
        let v = litVar l
        writeArray (seen s) v False
        writeSTRef pivotRef l
        writeSTRef pathRef =<< readArray (varReason s) v
        modifySTRef' counterRef (subtract 1)
        c <- readSTRef counterRef
        when (c > 0) step
  step
  pivot <- readSTRef pivotRef
  let asserting = litNeg pivot
  othersRaw <- readSTRef othersRef
  minimized <- minimize s othersRaw
  let learnt = orderLearnt asserting minimized
  btLevel <- computeBtLevel s minimized
  lbd <- computeLbd s learnt
  forM_ (litVar asserting : map litVar othersRaw) $ \v -> writeArray (seen s) v False
  pure (learnt, btLevel, lbd)

installLearnt :: Solver s -> [Int] -> Int -> ST s ()
installLearnt s learnt lbd = do
  case learnt of
    [u] -> do
      _ <- enqueue s u (-1)
      pure ()
    _ -> do
      cid <- newClause s learnt True
      cl <- getClause s cid
      writeSTRef (clsLbd cl) lbd
      claBumpActivity s cl
      attachClause s cid
      l0 <- readArray (clsLits cl) 0
      _ <- enqueue s l0 cid
      pure ()
  modifySTRef' (statLearn s) (+ 1)
  modifySTRef' (varInc s) (/ varDecayConst)
  modifySTRef' (claInc s) (/ claDecayConst)

analyzeFinal :: Solver s -> Int -> ST s [Int]
analyzeFinal s p = do
  dl <- currentLevel s
  if dl == 0
    then pure [p]
    else do
      writeArray (seen s) (litVar p) True
      lim <- readSTRef (trailLim s)
      n <- readSTRef (trailN s)
      let bottom = last lim
      outRef <- newSTRef [p]
      forM_ [n - 1, n - 2 .. bottom] $ \i -> do
        l <- readArray (trail s) i
        let x = litVar l
        sv <- readArray (seen s) x
        when sv $ do
          r <- readArray (varReason s) x
          if r < 0
            then modifySTRef' outRef (litNeg l :)
            else do
              cl <- getClause s r
              let lits = clsLits cl
                  sz = clsSize cl
              forM_ [1 .. sz - 1] $ \j -> do
                q <- readArray lits j
                lev <- readArray (varLevel s) (litVar q)
                when (lev > 0) $ writeArray (seen s) (litVar q) True
          writeArray (seen s) x False
      writeArray (seen s) (litVar p) False
      readSTRef outRef

minimize :: Solver s -> [Int] -> ST s [Int]
minimize s others = filterM (fmap not . redundant s) others

redundant :: Solver s -> Int -> ST s Bool
redundant s l = do
  r <- readArray (varReason s) (litVar l)
  if r < 0
    then pure False
    else do
      cl <- getClause s r
      let lits = clsLits cl
          sz = clsSize cl
      let chk j
            | j >= sz = pure True
            | otherwise = do
                q <- readArray lits j
                let v = litVar q
                sv <- readArray (seen s) v
                lev <- readArray (varLevel s) v
                if sv || lev == 0 then chk (j + 1) else pure False
      chk 1

orderLearnt :: Int -> [Int] -> [Int]
orderLearnt asserting [] = [asserting]
orderLearnt asserting others = asserting : others

computeBtLevel :: Solver s -> [Int] -> ST s Int
computeBtLevel s others =
  foldM (\acc l -> do
            lev <- readArray (varLevel s) (litVar l)
            pure (max acc lev)) 0 others

computeLbd :: Solver s -> [Int] -> ST s Int
computeLbd s learnt = do
  levels <- foldM (\acc l -> do
                      lev <- readArray (varLevel s) (litVar l)
                      pure (IntSet.insert lev acc)) IntSet.empty learnt
  pure (IntSet.size levels)

pickBranchVar :: Solver s -> ST s Int
pickBranchVar s = go
  where
    go = do
      empty <- heapIsEmpty (heapH s)
      if empty
        then pure (-1)
        else do
          v <- heapRemoveMax (heapH s)
          val <- varValue s v
          if val == 0 then pure v else go

search :: Solver s -> Int -> ST s (Maybe Bool)
search s confBudget = loop 0
  where
    loop confSoFar = do
      confl <- propagate s
      if confl >= 0
        then do
          modifySTRef' (statConf s) (+ 1)
          lvl <- currentLevel s
          if lvl == 0
            then do
              writeSTRef (okFlag s) False
              pure (Just False)
            else do
              (learnt, btLevel, lbd) <- analyze s confl
              cancelUntil s btLevel
              installLearnt s learnt lbd
              loop (confSoFar + 1)
        else do
          if confSoFar >= confBudget
            then do
              cancelUntil s 0
              pure Nothing
            else do
              maybeReduce s
              v <- pickBranchVar s
              if v < 0
                then pure (Just True)
                else do
                  modifySTRef' (statDec s) (+ 1)
                  pol <- readArray (polarity s) v
                  let l = if pol then posLit v else negLit v
                  newDecisionLevel s
                  _ <- enqueue s l (-1)
                  loop confSoFar

maybeReduce :: Solver s -> ST s ()
maybeReduce s = do
  nl <- readSTRef (nLearnts s)
  when (nl >= 2000) $ reduceDB s

reduceDB :: Solver s -> ST s ()
reduceDB s = do
  cids <- readSTRef (learnts s)
  alive <- filterM (\cid -> do cl <- getClause s cid; not <$> readSTRef (clsDead cl)) cids
  scored <- mapM (\cid -> do
                     cl <- getClause s cid
                     a <- readSTRef (clsAct cl)
                     lbd <- readSTRef (clsLbd cl)
                     locked <- isLocked s cid cl
                     pure (cid, cl, a, lbd, locked)) alive
  let removable = [ t | t@(_, _, _, lbd, locked) <- scored, not locked, lbd > 2 ]
      keepFixed = [ (cid, cl) | (cid, cl, _, lbd, locked) <- scored, locked || lbd <= 2 ]
      sortedByAct = sortByActAsc removable
      half = length sortedByAct `div` 2
      (toRemove, toKeepRest) = splitAt half sortedByAct
  forM_ toRemove $ \(_, cl, _, _, _) -> writeSTRef (clsDead cl) True
  let survivors = map (\(cid, cl) -> (cid, cl)) keepFixed
                  ++ map (\(cid, cl, _, _, _) -> (cid, cl)) toKeepRest
  writeSTRef (learnts s) (map fst survivors)
  writeSTRef (nLearnts s) (length survivors)
  modifySTRef' (statRemove s) (+ length toRemove)

sortByActAsc :: [(Cid, Clause s, Double, Int, Bool)] -> [(Cid, Clause s, Double, Int, Bool)]
sortByActAsc = sortByKey (\(_, _, a, _, _) -> a)

sortByKey :: Ord k => (a -> k) -> [a] -> [a]
sortByKey f = foldr insertBy []
  where
    insertBy x [] = [x]
    insertBy x (y : ys)
      | f x <= f y = x : y : ys
      | otherwise  = y : insertBy x ys

isLocked :: Solver s -> Cid -> Clause s -> ST s Bool
isLocked s cid cl = do
  l0 <- readArray (clsLits cl) 0
  let v = litVar l0
  vv <- varValue s v
  if vv == 0
    then pure False
    else do
      r <- readArray (varReason s) v
      pure (r == cid)

solveInternal :: Int -> [[Int]] -> ST s (Maybe [Bool], Stats)
solveInternal nv clausesIn = do
  s <- newSolver nv
  forM_ clausesIn (addClause s)
  ok0 <- readSTRef (okFlag s)
  result <-
    if not ok0
      then pure False
      else do
        confl0 <- propagate s
        if confl0 >= 0
          then do writeSTRef (okFlag s) False; pure False
          else runRestarts s 0
  model <-
    if result
      then Just <$> extractModel s
      else pure Nothing
  st <- collectStats s
  pure (model, st)

runRestarts :: Solver s -> Int -> ST s Bool
runRestarts s restartNo = do
  let budget = luby restartNo * 100
  outcome <- search s budget
  case outcome of
    Just verdict -> pure verdict
    Nothing -> do
      modifySTRef' (statRest s) (+ 1)
      runRestarts s (restartNo + 1)

extractModel :: Solver s -> ST s [Bool]
extractModel s =
  mapM (\v -> do
          vv <- varValue s v
          pure (vv /= -1)) [0 .. numVars s - 1]

collectStats :: Solver s -> ST s Stats
collectStats s = do
  d <- readSTRef (statDec s)
  c <- readSTRef (statConf s)
  p <- readSTRef (statProp s)
  r <- readSTRef (statRest s)
  l <- readSTRef (statLearn s)
  rm <- readSTRef (statRemove s)
  pure (Stats d c p r l rm)
