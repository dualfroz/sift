module Sift.Cdcl
  ( CdclResult(..)
  , solveCdcl
  , solveCdclStats
  , lubySequence
  ) where

import Control.Monad.ST (runST)
import qualified Data.Map.Strict as Map
import Sift.Types
import Sift.Stats
import Sift.Cdcl.Search (solveInternal, luby)

data CdclResult
  = CdclSat Assignment
  | CdclUnsat
  deriving (Eq, Show)

lubySequence :: Int -> [Int]
lubySequence k = map luby [0 .. k - 1]

solveCdcl :: CNF -> CdclResult
solveCdcl = fst . solveCdclStats

solveCdclStats :: CNF -> (CdclResult, Stats)
solveCdclStats (CNF cs) =
  let nv = maximum (0 : map varId (concatMap varsOfClause cs))
      dimacsClauses = map (map litToInt) cs
      (model, st) = runST (solveInternal nv dimacsClauses)
  in case model of
       Nothing    -> (CdclUnsat, st)
       Just bools ->
         let asn = Map.fromList [ (Var (i + 1), b) | (i, b) <- zip [0 ..] bools ]
         in (CdclSat asn, st)
