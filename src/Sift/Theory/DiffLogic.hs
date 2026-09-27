module Sift.Theory.DiffLogic
  ( DiffAtom(..)
  , DlProblem(..)
  , DlResult(..)
  , solveDl
  , feasible
  , evalAtom
  , dlModelSatisfies
  ) where

import Sift.Types
import Sift.Verify (satisfies)
import Sift.Cdcl (CdclResult(..), solveCdcl)
import qualified Data.Foldable as Foldable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data DiffAtom = DiffAtom
  { dlLhs   :: Int
  , dlRhs   :: Int
  , dlBound :: Int
  } deriving (Eq, Show)

data DlProblem = DlProblem
  { dlAtoms :: [DiffAtom]
  , dlCnf   :: CNF
  } deriving (Eq, Show)

data DlResult
  = DlSat (Map Int Int)
  | DlUnsat
  deriving (Eq, Show)

data Asserted = Asserted
  { acBlock :: Lit
  , acFrom  :: Int
  , acTo    :: Int
  , acW     :: Int
  } deriving (Eq, Show)

solveDl :: DlProblem -> DlResult
solveDl prob = loop iterLimit (dlCnf prob)
  where
    atoms = dlAtoms prob
    numAtoms = length atoms
    iterLimit :: Int
    iterLimit = if numAtoms >= 20 then 1000000 else 2 ^ numAtoms + 1
    loop budget cnf
      | budget <= 0 = DlUnsat
      | otherwise =
      case solveCdcl cnf of
        CdclUnsat -> DlUnsat
        CdclSat model ->
          let asserted =
                [ assertionOf i atom model | (i, atom) <- zip [1 ..] atoms ]
          in case feasible asserted of
               Right potentials -> DlSat potentials
               Left core ->
                 let blocking = map acBlock core
                 in loop (budget - 1) (CNF (blocking : clauses cnf))

assertionOf :: Int -> DiffAtom -> Assignment -> Asserted
assertionOf i (DiffAtom lhs rhs bound) model =
  if Map.findWithDefault True (Var i) model
    then Asserted (negLit (Var i)) rhs lhs bound
    else Asserted (posLit (Var i)) lhs rhs (negate bound - 1)

feasible :: [Asserted] -> Either [Asserted] (Map Int Int)
feasible asserted =
  case changed of
    [] -> Right distV
    (x : _) ->
      let onCycle = walkBack (length nodes) x
      in Left (traceCycle onCycle)
  where
    nodes = Set.toList (Set.fromList (concatMap (\a -> [acFrom a, acTo a]) asserted))
    dist0 = Map.fromList [ (nd, 0) | nd <- nodes ]
    (distV, predsV) = iterateRelax (length nodes) asserted dist0 Map.empty
    (distV1, predsV1) = relaxRound asserted distV predsV
    changed = [ nd | nd <- nodes, Map.findWithDefault 0 nd distV1 < Map.findWithDefault 0 nd distV ]

    walkBack :: Int -> Int -> Int
    walkBack 0 node = node
    walkBack k node =
      case Map.lookup node predsV1 of
        Just e  -> walkBack (k - 1) (acFrom e)
        Nothing -> node

    traceCycle :: Int -> [Asserted]
    traceCycle startNode =
      case go (length nodes + 1) startNode [] of
        Just cyc -> cyc
        Nothing  -> asserted
      where
        go steps cur acc
          | steps < 0 = Nothing
          | otherwise =
              case Map.lookup cur predsV1 of
                Nothing   -> Nothing
                Just edge ->
                  let prev = acFrom edge
                  in if prev == startNode
                       then Just (edge : acc)
                       else go (steps - 1) prev (edge : acc)

iterateRelax :: Int -> [Asserted] -> Map Int Int -> Map Int Asserted -> (Map Int Int, Map Int Asserted)
iterateRelax 0 _ dist preds = (dist, preds)
iterateRelax k edges dist preds =
  let (dist', preds') = relaxRound edges dist preds
  in iterateRelax (k - 1) edges dist' preds'

relaxRound :: [Asserted] -> Map Int Int -> Map Int Asserted -> (Map Int Int, Map Int Asserted)
relaxRound edges dist preds = Foldable.foldl' relax (dist, preds) edges
  where
    relax (d, p) a =
      let du = Map.findWithDefault 0 (acFrom a) d
          dv = Map.findWithDefault 0 (acTo a) d
      in if du + acW a < dv
           then (Map.insert (acTo a) (du + acW a) d, Map.insert (acTo a) a p)
           else (d, p)

evalAtom :: Map Int Int -> DiffAtom -> Bool
evalAtom assignment (DiffAtom lhs rhs bound) =
  Map.findWithDefault 0 lhs assignment - Map.findWithDefault 0 rhs assignment <= bound

dlModelSatisfies :: DlProblem -> Map Int Int -> Bool
dlModelSatisfies prob assignment =
  satisfies atomTruth (dlCnf prob)
  where
    atomTruth = Map.fromList
      [ (Var i, evalAtom assignment atom) | (i, atom) <- zip [1 ..] (dlAtoms prob) ]
