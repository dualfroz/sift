module Sift.Preprocess
  ( PreResult(..)
  , unitPropagate
  , pureLiteralElim
  , subsume
  , selfSubsume
  , preprocess
  , reconstruct
  ) where

import Sift.Types
import qualified Data.Foldable as Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data PreResult
  = Unsatisfiable
  | Simplified [Lit] CNF
  deriving (Eq, Show)

toSets :: CNF -> [Set Lit]
toSets (CNF cs) = map Set.fromList cs

fromSets :: [Set Lit] -> CNF
fromSets = CNF . map Set.toList

unitPropagate :: CNF -> Maybe ([Lit], CNF)
unitPropagate cnf = go [] (toSets cnf)
  where
    go assigned clauses
      | any Set.null clauses = Nothing
      | otherwise =
          case [ Set.findMin c | c <- clauses, Set.size c == 1 ] of
            []      -> Just (reverse assigned, fromSets clauses)
            (l : _) ->
              let clauses' = propagateOne l clauses
              in go (l : assigned) clauses'

propagateOne :: Lit -> [Set Lit] -> [Set Lit]
propagateOne l = foldr step []
  where
    step c acc
      | l `Set.member` c        = acc
      | neg l `Set.member` c    = Set.delete (neg l) c : acc
      | otherwise               = c : acc

pureLiteralElim :: CNF -> ([Lit], CNF)
pureLiteralElim cnf = go [] (toSets cnf)
  where
    go assigned clauses =
      case pureLiterals clauses of
        []   -> (reverse assigned, fromSets clauses)
        pures ->
          let clauses' = Foldable.foldl' (flip removeSatisfied) clauses pures
          in go (reverse pures ++ assigned) clauses'

pureLiterals :: [Set Lit] -> [Lit]
pureLiterals clauses =
  [ l
  | l <- Set.toList allLits
  , not (neg l `Set.member` allLits)
  ]
  where
    allLits = Set.unions clauses

removeSatisfied :: Lit -> [Set Lit] -> [Set Lit]
removeSatisfied l = filter (not . Set.member l)

subsume :: CNF -> CNF
subsume cnf = fromSets (dropSubsumed (dedupe (toSets cnf)))

dedupe :: [Set Lit] -> [Set Lit]
dedupe = Set.toList . Set.fromList

dropSubsumed :: [Set Lit] -> [Set Lit]
dropSubsumed clauses =
  [ c | c <- clauses, not (any (subsumedBy c) clauses) ]
  where
    subsumedBy c d = d /= c && d `Set.isSubsetOf` c

selfSubsume :: CNF -> CNF
selfSubsume cnf = fromSets (fixSelf (toSets cnf))

fixSelf :: [Set Lit] -> [Set Lit]
fixSelf clauses =
  let stepped = map (strengthen clauses) clauses
  in if stepped == clauses then clauses else fixSelf stepped

strengthen :: [Set Lit] -> Set Lit -> Set Lit
strengthen clauses c = Foldable.foldl' tryLit c (Set.toList c)
  where
    tryLit acc l
      | any (resolvesAway l acc) clauses = Set.delete l acc
      | otherwise                        = acc
    resolvesAway l acc d =
      neg l `Set.member` d
        && Set.delete (neg l) d `Set.isSubsetOf` Set.delete l acc

preprocess :: CNF -> PreResult
preprocess cnf = loop [] cnf
  where
    loop fixed current =
      case unitPropagate current of
        Nothing -> Unsatisfiable
        Just (units, afterUnits) ->
          let (pures, afterPures) = pureLiteralElim afterUnits
              afterSub  = subsume afterPures
              afterSelf = subsume (selfSubsume afterSub)
              fixed'    = fixed ++ units ++ pures
          in if clauseSetEq afterSelf current && null units && null pures
               then Simplified fixed' afterSelf
               else loop fixed' afterSelf

clauseSetEq :: CNF -> CNF -> Bool
clauseSetEq a b = Set.fromList (toSets a) == Set.fromList (toSets b)

reconstruct :: [Lit] -> Assignment -> Assignment
reconstruct fixed asn =
  Foldable.foldl' (\m l -> Map.insert (litVar l) (litSign l) m) asn fixed
