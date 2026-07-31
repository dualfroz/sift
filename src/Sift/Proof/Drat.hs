{-# LANGUAGE FlexibleContexts #-}
module Sift.Proof.Drat
  ( ProofResult(..)
  , solveProof
  , verifyProof
  , isRup
  , renderProof
  ) where

import Control.Monad (forM_)
import Control.Monad.ST (ST, runST)
import Data.STRef
import Data.Array.ST (readArray)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import Sift.Types
import qualified Sift.Cdcl.State as St
import Sift.Cdcl.Search
  ( propagate, analyze, pickBranchVar, maybeReduce, installLearnt, luby )

data ProofResult
  = ProofSat Assignment
  | ProofUnsat [Clause]
  deriving (Eq, Show)

solveProof :: CNF -> ProofResult
solveProof (CNF cs) = runST $ do
  let nv = maximum (0 : map varId (concatMap varsOfClause cs))
  s <- St.newSolver nv
  proofRef <- newSTRef []
  forM_ cs (St.addClause s . map litToInt)
  ok0 <- readSTRef (St.okFlag s)
  if not ok0
    then pure (ProofUnsat [[]])
    else do
      confl0 <- propagate s
      if confl0 >= 0
        then pure (ProofUnsat [[]])
        else do
          verdict <- runRestarts s proofRef 0
          if verdict
            then do
              model <- extractAssignment s
              pure (ProofSat model)
            else do
              recorded <- reverse <$> readSTRef proofRef
              pure (ProofUnsat (map toClause recorded ++ [[]]))

toClause :: [Int] -> Clause
toClause = map (litFromInt . St.dimacsOfLit)

runRestarts :: St.Solver s -> STRef s [[Int]] -> Int -> ST s Bool
runRestarts s proofRef restartNo = do
  let budget = luby restartNo * 100
  outcome <- proofSearch s proofRef budget
  case outcome of
    Just verdict -> pure verdict
    Nothing -> do
      modifySTRef' (St.statRest s) (+ 1)
      runRestarts s proofRef (restartNo + 1)

proofSearch :: St.Solver s -> STRef s [[Int]] -> Int -> ST s (Maybe Bool)
proofSearch s proofRef confBudget = loop 0
  where
    loop confSoFar = do
      confl <- propagate s
      if confl >= 0
        then do
          modifySTRef' (St.statConf s) (+ 1)
          lvl <- St.currentLevel s
          if lvl == 0
            then pure (Just False)
            else do
              (learnt, btLevel, lbd) <- analyze s confl
              modifySTRef' proofRef (learnt :)
              St.cancelUntil s btLevel
              installLearnt s learnt lbd
              loop (confSoFar + 1)
        else
          if confSoFar >= confBudget
            then do St.cancelUntil s 0; pure Nothing
            else do
              maybeReduce s
              v <- pickBranchVar s
              if v < 0
                then pure (Just True)
                else do
                  modifySTRef' (St.statDec s) (+ 1)
                  pol <- readArray (St.polarity s) v
                  let l = if pol then St.posLit v else St.negLit v
                  St.newDecisionLevel s
                  _ <- St.enqueue s l (-1)
                  loop confSoFar

extractAssignment :: St.Solver s -> ST s Assignment
extractAssignment s = do
  pairs <- mapM (\v -> do
                    vv <- St.varValue s v
                    pure (Var (v + 1), vv /= -1)) [0 .. St.numVars s - 1]
  pure (Map.fromList pairs)

verifyProof :: CNF -> [Clause] -> Bool
verifyProof (CNF orig) = go orig
  where
    go _ [] = False
    go formula (c : rest)
      | not (isRup formula c) = False
      | null c                = True
      | otherwise             = go (c : formula) rest

isRup :: [Clause] -> Clause -> Bool
isRup formula lemma =
  propagatesToConflict formula (map neg lemma)

propagatesToConflict :: [Clause] -> [Lit] -> Bool
propagatesToConflict clauses0 assumed =
  case assignAll Map.empty assumed of
    Nothing -> True
    Just a0 -> loop a0
  where
    clauses = normalizeClauses clauses0
    assignAll a []       = Just a
    assignAll a (l : ls) = case extend a l of
      Nothing -> Nothing
      Just a' -> assignAll a' ls
    extend a l = case Map.lookup (litVar l) a of
      Just b
        | b == litSign l -> Just a
        | otherwise      -> Nothing
      Nothing -> Just (Map.insert (litVar l) (litSign l) a)
    loop a
      | any (falsifiedBy a) clauses = True
      | otherwise =
          case pickUnit a clauses of
            Nothing -> False
            Just l  -> case extend a l of
              Nothing -> True
              Just a' -> loop a'

normalizeClauses :: [Clause] -> [Clause]
normalizeClauses = concatMap norm
  where
    norm c =
      let deduped = nub c
      in if any (\l -> neg l `elem` deduped) deduped then [] else [deduped]

falsifiedBy :: Assignment -> Clause -> Bool
falsifiedBy a c = all (\l -> litValue a l == Just False) c

pickUnit :: Assignment -> [Clause] -> Maybe Lit
pickUnit a = firstJust . map (unitLiteral a)
  where
    firstJust []             = Nothing
    firstJust (Just l : _)   = Just l
    firstJust (Nothing : xs) = firstJust xs

unitLiteral :: Assignment -> Clause -> Maybe Lit
unitLiteral a c =
  case [ l | l <- c, litValue a l == Nothing ] of
    [l] | not (any (\k -> litValue a k == Just True) c) -> Just l
    _   -> Nothing

renderProof :: [Clause] -> String
renderProof = unlines . map renderClause
  where
    renderClause c = unwords (map (show . litToInt) c ++ ["0"])
