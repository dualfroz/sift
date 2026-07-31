{-# LANGUAGE FlexibleContexts #-}
module Sift.Cdcl.Incremental
  ( IncResult(..)
  , solveAssuming
  , solveManyAssuming
  ) where

import Control.Monad (forM, forM_)
import Control.Monad.ST (ST, runST)
import Data.STRef
import Data.Array.ST
import Data.List (nub)
import qualified Data.Map.Strict as Map
import Sift.Types (Var(..), Lit, CNF(..), Assignment, litToInt, litFromInt, varsOfClause, varId)
import Sift.Cdcl.State
import Sift.Cdcl.Search (propagate, analyze, analyzeFinal, pickBranchVar, maybeReduce, installLearnt, luby)

data IncResult
  = IncSat Assignment
  | IncUnsat [Lit]
  deriving (Eq, Show)

data StepOutcome
  = StepSat
  | StepUnsat [Int]
  | StepRestart

data AssumeStep
  = AssumeConflict [Int]
  | AssumeLit Int
  | AssumeDone

solveAssuming :: CNF -> [Lit] -> IncResult
solveAssuming cnf assumps =
  case solveManyAssuming cnf [assumps] of
    [r] -> r
    _   -> IncUnsat []

solveManyAssuming :: CNF -> [[Lit]] -> [IncResult]
solveManyAssuming (CNF cs) queries = runST $ do
  let clauseMax = maximum (0 : map varId (concatMap varsOfClause cs))
      assumpMax = maximum (0 : [ abs (litToInt l) | q <- queries, l <- q ])
      nv = max clauseMax assumpMax
  s <- newSolver nv
  forM_ cs (addClause s . map litToInt)
  forM queries $ \assumps -> do
    outcome <- solveOne s (map (litOfDimacs . litToInt) assumps)
    case outcome of
      Right () -> do
        model <- extractAssignment s
        pure (IncSat model)
      Left core ->
        pure (IncUnsat (nub (map (litFromInt . dimacsOfLit . litNeg) core)))

solveOne :: Solver s -> [Int] -> ST s (Either [Int] ())
solveOne s assumps = do
  cancelUntil s 0
  ok <- readSTRef (okFlag s)
  if not ok
    then pure (Left [])
    else do
      confl0 <- propagate s
      if confl0 >= 0
        then do writeSTRef (okFlag s) False; pure (Left [])
        else runRestarts 0
  where
    runRestarts restartNo = do
      let budget = lubyBudget restartNo
      outcome <- searchAssuming s assumps budget
      case outcome of
        StepSat        -> pure (Right ())
        StepUnsat core -> pure (Left core)
        StepRestart    -> do
          modifySTRef' (statRest s) (+ 1)
          runRestarts (restartNo + 1)

lubyBudget :: Int -> Int
lubyBudget restartNo = luby restartNo * 100

searchAssuming :: Solver s -> [Int] -> Int -> ST s StepOutcome
searchAssuming s assumps confBudget = loop 0
  where
    loop confSoFar = do
      confl <- propagate s
      if confl >= 0
        then do
          modifySTRef' (statConf s) (+ 1)
          lvl <- currentLevel s
          if lvl == 0
            then do writeSTRef (okFlag s) False; pure (StepUnsat [])
            else do
              (learnt, btLevel, lbd) <- analyze s confl
              cancelUntil s btLevel
              installLearnt s learnt lbd
              loop (confSoFar + 1)
        else
          if confSoFar >= confBudget
            then do cancelUntil s 0; pure StepRestart
            else do
              maybeReduce s
              step <- nextAssumption s assumps
              case step of
                AssumeConflict core -> pure (StepUnsat core)
                AssumeLit next -> do
                  newDecisionLevel s
                  _ <- enqueue s next (-1)
                  loop confSoFar
                AssumeDone -> do
                  v <- pickBranchVar s
                  if v < 0
                    then pure StepSat
                    else do
                      modifySTRef' (statDec s) (+ 1)
                      pol <- readArray (polarity s) v
                      let l = if pol then posLit v else negLit v
                      newDecisionLevel s
                      _ <- enqueue s l (-1)
                      loop confSoFar

nextAssumption :: Solver s -> [Int] -> ST s AssumeStep
nextAssumption s assumps = go
  where
    total = length assumps
    go = do
      dl <- currentLevel s
      if dl >= total
        then pure AssumeDone
        else do
          let p = assumps !! dl
          v <- litValueInt s p
          if v == 1
            then do newDecisionLevel s; go
            else if v == -1
              then do
                core <- analyzeFinal s (litNeg p)
                pure (AssumeConflict core)
              else pure (AssumeLit p)

extractAssignment :: Solver s -> ST s Assignment
extractAssignment s = do
  pairs <- forM [0 .. numVars s - 1] $ \v -> do
    vv <- varValue s v
    pure (Var (v + 1), vv /= -1)
  pure (Map.fromList pairs)
