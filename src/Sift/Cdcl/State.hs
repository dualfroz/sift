{-# LANGUAGE FlexibleContexts #-}
module Sift.Cdcl.State
  ( Solver(..)
  , Clause(..)
  , Watcher(..)
  , Cid
  , litOfDimacs
  , dimacsOfLit
  , litVar
  , litSignPos
  , litNeg
  , posLit
  , negLit
  , newSolver
  , litValueInt
  , varValue
  , currentLevel
  , newDecisionLevel
  , enqueue
  , cancelUntil
  , getClause
  , newClause
  , attachClause
  , addClause
  , varBumpActivity
  , rescaleActivities
  , claBumpActivity
  , claRescale
  , modifyWatch
  , varDecayConst
  , claDecayConst
  ) where

import Control.Monad (when, forM_, foldM)
import Control.Monad.ST (ST)
import Data.Bits (xor)
import Data.STRef
import Data.Array.ST
import Data.List (sort)
import Sift.Cdcl.Heap

type Cid = Int

data Watcher = Watcher !Cid !Int

data Clause s = Clause
  { clsLits   :: STUArray s Int Int
  , clsSize   :: !Int
  , clsLearnt :: !Bool
  , clsAct    :: STRef s Double
  , clsLbd    :: STRef s Int
  , clsDead   :: STRef s Bool
  }

data Solver s = Solver
  { numVars    :: !Int
  , value      :: STUArray s Int Int
  , varLevel   :: STUArray s Int Int
  , varReason  :: STUArray s Int Int
  , polarity   :: STUArray s Int Bool
  , activity   :: STUArray s Int Double
  , seen       :: STUArray s Int Bool
  , trail      :: STUArray s Int Int
  , trailN     :: STRef s Int
  , qhead      :: STRef s Int
  , trailLim   :: STRef s [Int]
  , watches    :: STArray s Int [Watcher]
  , clauseArr  :: STRef s (STArray s Int (Clause s))
  , clauseN    :: STRef s Int
  , learnts    :: STRef s [Cid]
  , nLearnts   :: STRef s Int
  , heapH      :: VarHeap s
  , varInc     :: STRef s Double
  , claInc     :: STRef s Double
  , okFlag     :: STRef s Bool
  , statDec    :: STRef s Int
  , statConf   :: STRef s Int
  , statProp   :: STRef s Int
  , statRest   :: STRef s Int
  , statLearn  :: STRef s Int
  , statRemove :: STRef s Int
  }

varDecayConst :: Double
varDecayConst = 0.95

claDecayConst :: Double
claDecayConst = 0.999

valUndef, valTrue, valFalse :: Int
valUndef = 0
valTrue  = 1
valFalse = -1

litOfDimacs :: Int -> Int
litOfDimacs n
  | n > 0     = 2 * (n - 1)
  | otherwise = 2 * (negate n - 1) + 1

dimacsOfLit :: Int -> Int
dimacsOfLit l =
  let v = litVar l + 1
  in if litSignPos l then v else negate v

litVar :: Int -> Int
litVar l = l `div` 2

litSignPos :: Int -> Bool
litSignPos l = even l

litNeg :: Int -> Int
litNeg l = l `xor` 1

posLit :: Int -> Int
posLit v = 2 * v

negLit :: Int -> Int
negLit v = 2 * v + 1

newSolver :: Int -> ST s (Solver s)
newSolver n = do
  let nv = max 1 n
  val   <- newArray (0, nv - 1) valUndef
  lev   <- newArray (0, nv - 1) (-1)
  rsn   <- newArray (0, nv - 1) (-1)
  pol   <- newArray (0, nv - 1) False
  act   <- newArray (0, nv - 1) 0
  sn    <- newArray (0, nv - 1) False
  tr    <- newArray (0, nv - 1) 0
  trN   <- newSTRef 0
  qh    <- newSTRef 0
  tlim  <- newSTRef []
  ws    <- newArray (0, 2 * nv - 1) []
  cap0  <- newArray (0, 15) (error "empty clause slot") :: ST s (STArray s Int (Clause s))
  carr  <- newSTRef cap0
  cn    <- newSTRef 0
  lrn   <- newSTRef []
  nlrn  <- newSTRef 0
  hp    <- newHeap nv act
  forM_ [0 .. n - 1] $ \v -> heapInsert hp v
  vinc  <- newSTRef 1.0
  cinc  <- newSTRef 1.0
  ok    <- newSTRef True
  sd    <- newSTRef 0
  sc    <- newSTRef 0
  sp    <- newSTRef 0
  sr    <- newSTRef 0
  sl    <- newSTRef 0
  srm   <- newSTRef 0
  pure Solver
    { numVars = n
    , value = val, varLevel = lev, varReason = rsn, polarity = pol
    , activity = act, seen = sn, trail = tr, trailN = trN, qhead = qh
    , trailLim = tlim, watches = ws, clauseArr = carr, clauseN = cn
    , learnts = lrn, nLearnts = nlrn, heapH = hp, varInc = vinc, claInc = cinc
    , okFlag = ok, statDec = sd, statConf = sc, statProp = sp, statRest = sr
    , statLearn = sl, statRemove = srm
    }

varValue :: Solver s -> Int -> ST s Int
varValue s v = readArray (value s) v

litValueInt :: Solver s -> Int -> ST s Int
litValueInt s l = do
  vv <- readArray (value s) (litVar l)
  if vv == valUndef
    then pure valUndef
    else pure (if litSignPos l then vv else negate vv)

currentLevel :: Solver s -> ST s Int
currentLevel s = length <$> readSTRef (trailLim s)

newDecisionLevel :: Solver s -> ST s ()
newDecisionLevel s = do
  n <- readSTRef (trailN s)
  modifySTRef' (trailLim s) (n :)

enqueue :: Solver s -> Int -> Cid -> ST s Bool
enqueue s l reason = do
  v <- litValueInt s l
  if v == valTrue
    then pure True
    else if v == valFalse
      then pure False
      else do
        let var = litVar l
        writeArray (value s) var (if litSignPos l then valTrue else valFalse)
        lvl <- currentLevel s
        writeArray (varLevel s) var lvl
        writeArray (varReason s) var reason
        writeArray (polarity s) var (litSignPos l)
        n <- readSTRef (trailN s)
        writeArray (trail s) n l
        writeSTRef (trailN s) (n + 1)
        pure True

cancelUntil :: Solver s -> Int -> ST s ()
cancelUntil s lvl = do
  lim <- readSTRef (trailLim s)
  let curLvl = length lim
  when (curLvl > lvl) $ do
    n <- readSTRef (trailN s)
    let boundary = lim !! (curLvl - lvl - 1)
    forM_ [n - 1, n - 2 .. boundary] $ \i -> do
      l <- readArray (trail s) i
      let var = litVar l
      writeArray (value s) var valUndef
      heapInsert (heapH s) var
    writeSTRef (trailN s) boundary
    writeSTRef (qhead s) boundary
    writeSTRef (trailLim s) (drop (curLvl - lvl) lim)

getClause :: Solver s -> Cid -> ST s (Clause s)
getClause s cid = do
  arr <- readSTRef (clauseArr s)
  readArray arr cid

pushClauseRef :: Solver s -> Clause s -> ST s Cid
pushClauseRef s cl = do
  arr <- readSTRef (clauseArr s)
  cnt <- readSTRef (clauseN s)
  (lo, hi) <- getBounds arr
  arr' <-
    if cnt > hi
      then do
        bigger <- newArray (lo, 2 * (hi + 1) - 1) (error "empty clause slot")
        forM_ [lo .. hi] $ \i -> readArray arr i >>= writeArray bigger i
        writeSTRef (clauseArr s) bigger
        pure bigger
      else pure arr
  writeArray arr' cnt cl
  writeSTRef (clauseN s) (cnt + 1)
  pure cnt

newClause :: Solver s -> [Int] -> Bool -> ST s Cid
newClause s lits learnt = do
  let sz = length lits
  la  <- newListArray (0, sz - 1) lits
  act <- newSTRef 0
  lbd <- newSTRef 0
  dead <- newSTRef False
  let cl = Clause la sz learnt act lbd dead
  cid <- pushClauseRef s cl
  when learnt $ do
    modifySTRef' (learnts s) (cid :)
    modifySTRef' (nLearnts s) (+ 1)
  pure cid

attachClause :: Solver s -> Cid -> ST s ()
attachClause s cid = do
  cl <- getClause s cid
  l0 <- readArray (clsLits cl) 0
  l1 <- readArray (clsLits cl) 1
  modifyWatch s (litNeg l0) (Watcher cid l1)
  modifyWatch s (litNeg l1) (Watcher cid l0)

modifyWatch :: Solver s -> Int -> Watcher -> ST s ()
modifyWatch s l w = do
  old <- readArray (watches s) l
  writeArray (watches s) l (w : old)

cleanClause :: [Int] -> Maybe [Int]
cleanClause lits = go (sort lits)
  where
    go [] = Just []
    go [x] = Just [x]
    go (x : y : rest)
      | x == y            = go (y : rest)
      | x == litNeg y     = Nothing
      | otherwise         = (x :) <$> go (y : rest)

addClause :: Solver s -> [Int] -> ST s ()
addClause s dimacsLits = do
  ok <- readSTRef (okFlag s)
  when ok $
    case cleanClause (map litOfDimacs dimacsLits) of
      Nothing -> pure ()
      Just ls -> do
        anyTrue <- foldM (\acc l -> if acc then pure True else (== valTrue) <$> litValueInt s l) False ls
        if anyTrue
          then pure ()
          else do
            kept <- filterFalse s ls
            case kept of
              [] -> writeSTRef (okFlag s) False
              [u] -> do
                r <- enqueue s u (-1)
                when (not r) $ writeSTRef (okFlag s) False
              _ -> do
                cid <- newClause s kept False
                attachClause s cid

filterFalse :: Solver s -> [Int] -> ST s [Int]
filterFalse s = go
  where
    go [] = pure []
    go (l : ls) = do
      v <- litValueInt s l
      rest <- go ls
      pure (if v == valFalse then rest else l : rest)

varBumpActivity :: Solver s -> Int -> ST s ()
varBumpActivity s v = do
  inc <- readSTRef (varInc s)
  a <- readArray (activity s) v
  let a' = a + inc
  writeArray (activity s) v a'
  when (a' > 1e100) $ rescaleActivities s
  heapIncrease (heapH s) v

rescaleActivities :: Solver s -> ST s ()
rescaleActivities s = do
  forM_ [0 .. numVars s - 1] $ \v -> do
    a <- readArray (activity s) v
    writeArray (activity s) v (a * 1e-100)
  modifySTRef' (varInc s) (* 1e-100)

claBumpActivity :: Solver s -> Clause s -> ST s ()
claBumpActivity s cl = do
  inc <- readSTRef (claInc s)
  a <- readSTRef (clsAct cl)
  let a' = a + inc
  writeSTRef (clsAct cl) a'
  when (a' > 1e20) $ claRescale s

claRescale :: Solver s -> ST s ()
claRescale s = do
  cids <- readSTRef (learnts s)
  forM_ cids $ \cid -> do
    cl <- getClause s cid
    a <- readSTRef (clsAct cl)
    writeSTRef (clsAct cl) (a * 1e-20)
  modifySTRef' (claInc s) (* 1e-20)
