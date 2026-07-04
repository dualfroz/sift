module Sift.Solver
  ( Result(..)
  , solve
  , dpll
  ) where

import Sift.Types
import Sift.Verify (completeModel)
import Data.List (maximumBy, nub)
import Data.Ord (comparing)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data Result
  = Sat Assignment
  | Unsat
  deriving (Eq, Show)

solve :: CNF -> Result
solve cnf@(CNF cs) =
  case dpll cs Map.empty of
    Nothing  -> Unsat
    Just asn -> Sat (completeModel cnf asn)

dpll :: [Clause] -> Assignment -> Maybe Assignment
dpll original asn =
  case reduce asn original of
    Nothing -> Nothing
    Just cs
      | null cs   -> Just asn
      | otherwise ->
          case findUnit cs of
            Just l  -> dpll original (assign l asn)
            Nothing ->
              case findPure cs of
                Just l  -> dpll original (assign l asn)
                Nothing ->
                  let l = chooseLit cs
                  in case dpll original (assign l asn) of
                       Just m  -> Just m
                       Nothing -> dpll original (assign (neg l) asn)

assign :: Lit -> Assignment -> Assignment
assign l = Map.insert (litVar l) (litSign l)

reduce :: Assignment -> [Clause] -> Maybe [Clause]
reduce asn = fmap reverse . foldl step (Just [])
  where
    step Nothing _ = Nothing
    step (Just acc) c
      | any ((== Just True) . litValue asn) c = Just acc
      | otherwise =
          let remaining = filter ((== Nothing) . litValue asn) c
          in if null remaining then Nothing else Just (remaining : acc)

findUnit :: [Clause] -> Maybe Lit
findUnit cs = case [ l | [l] <- cs ] of
  (l:_) -> Just l
  []    -> Nothing

findPure :: [Clause] -> Maybe Lit
findPure cs =
  case [ Lit v s | (v, [s]) <- Map.toList signsByVar ] of
    (l:_) -> Just l
    []    -> Nothing
  where
    signsByVar :: Map Var [Bool]
    signsByVar =
      Map.map nub (Map.fromListWith (++) [ (litVar l, [litSign l]) | l <- concat cs ])

chooseLit :: [Clause] -> Lit
chooseLit cs = fst (maximumBy (comparing snd) (Map.toList counts))
  where
    counts :: Map Lit Int
    counts = Map.fromListWith (+) [ (l, 1) | l <- concat cs ]
