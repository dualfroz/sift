module Sift.Preprocess.Bve
  ( BveResult(..)
  , bve
  , reconstructBve
  ) where

import Sift.Types
import qualified Data.Foldable as Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data BveResult = BveResult
  { bveCnf        :: CNF
  , bveEliminated :: [(Var, [Clause])]
  } deriving (Eq, Show)

bve :: CNF -> BveResult
bve cnf =
  let (finalClauses, elimsRev) = Foldable.foldl' consider (toSets cnf, []) (allVars cnf)
  in BveResult (fromSets finalClauses) (reverse elimsRev)
  where
    consider (clauses, elims) x =
      let (posC, rest0) = partition' (Set.member (posLit x)) clauses
          (negC, rest)  = partition' (Set.member (negLit x)) rest0
      in if null posC && null negC
           then (clauses, elims)
           else
             let resolvents =
                   dedupe
                     [ r
                     | p <- posC, q <- negC
                     , Just r <- [resolve x p q] ]
             in if length resolvents <= length posC + length negC
                  then ( rest ++ resolvents
                       , (x, map Set.toList (posC ++ negC)) : elims )
                  else (clauses, elims)

partition' :: (a -> Bool) -> [a] -> ([a], [a])
partition' p xs = (filter p xs, filter (not . p) xs)

resolve :: Var -> Set Lit -> Set Lit -> Maybe (Set Lit)
resolve x p q =
  let merged = Set.union (Set.delete (posLit x) p) (Set.delete (negLit x) q)
  in if isTautology merged then Nothing else Just merged

isTautology :: Set Lit -> Bool
isTautology c = any (\l -> neg l `Set.member` c) (Set.toList c)

dedupe :: [Set Lit] -> [Set Lit]
dedupe = Set.toList . Set.fromList

toSets :: CNF -> [Set Lit]
toSets (CNF cs) = map Set.fromList cs

fromSets :: [Set Lit] -> CNF
fromSets = CNF . map Set.toList

reconstructBve :: BveResult -> Assignment -> Assignment
reconstructBve result asn =
  Foldable.foldl' restoreVar (seedFreeVars result asn) (reverse (bveEliminated result))
  where
    restoreVar acc (x, cls) =
      let posNeedsTrue =
            any (\c -> posLit x `elem` c && not (satisfiedByOthers x c acc)) cls
      in Map.insert x posNeedsTrue acc

seedFreeVars :: BveResult -> Assignment -> Assignment
seedFreeVars result asn =
  Foldable.foldl' (\acc v -> Map.insertWith (\_ old -> old) v True acc) asn freeVars
  where
    eliminated = Set.fromList (map fst (bveEliminated result))
    freeVars =
      [ v
      | (_, cls) <- bveEliminated result
      , c <- cls, l <- c
      , let v = litVar l
      , not (Set.member v eliminated) ]

satisfiedByOthers :: Var -> Clause -> Assignment -> Bool
satisfiedByOthers x c asn =
  any (\l -> litVar l /= x && litValue asn l == Just True) c
