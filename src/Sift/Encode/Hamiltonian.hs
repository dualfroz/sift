module Sift.Encode.Hamiltonian
  ( hamCell
  , hamiltonianPath
  , hamiltonianCycle
  , decodeHamiltonian
  , validHamiltonianPath
  , validHamiltonianCycle
  ) where

import Sift.Types
import Sift.Encode.Cardinality
import Sift.Encode.Coloring (Graph(..))
import Data.List (sortOn)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

hamCell :: Int -> Int -> Int -> Var
hamCell n vertex position = Var ((vertex - 1) * n + position)

adjacency :: Graph -> Set (Int, Int)
adjacency (Graph _ edges) =
  Set.fromList (concat [ [(u, w), (w, u)] | (u, w) <- edges ])

positionConstraints :: Int -> [Clause]
positionConstraints n =
  concat [ exactlyOne [ posLit (hamCell n vertex position) | vertex <- [1 .. n] ]
         | position <- [1 .. n] ]
  ++
  concat [ exactlyOne [ posLit (hamCell n vertex position) | position <- [1 .. n] ]
         | vertex <- [1 .. n] ]

forbidNonAdjacent :: Int -> Set (Int, Int) -> Int -> Int -> [Clause]
forbidNonAdjacent n adj fromPos toPos =
  [ [ neg (posLit (hamCell n u fromPos)), neg (posLit (hamCell n w toPos)) ]
  | u <- [1 .. n], w <- [1 .. n], u /= w
  , not (Set.member (u, w) adj) ]

hamiltonianPath :: Graph -> CNF
hamiltonianPath g@(Graph n _) =
  CNF (positionConstraints n ++ stepClauses)
  where
    adj = adjacency g
    stepClauses = concat [ forbidNonAdjacent n adj i (i + 1) | i <- [1 .. n - 1] ]

hamiltonianCycle :: Graph -> CNF
hamiltonianCycle g@(Graph n _) =
  CNF (positionConstraints n ++ stepClauses ++ wrapClauses)
  where
    adj = adjacency g
    stepClauses = concat [ forbidNonAdjacent n adj i (i + 1) | i <- [1 .. n - 1] ]
    wrapClauses = forbidNonAdjacent n adj n 1

decodeHamiltonian :: Int -> Assignment -> [Int]
decodeHamiltonian n asn =
  map snd (sortOn fst
    [ (position, vertex)
    | position <- [1 .. n], vertex <- [1 .. n]
    , Map.findWithDefault False (hamCell n vertex position) asn ])

isPermutation :: Int -> [Int] -> Bool
isPermutation n xs = Set.fromList xs == Set.fromList [1 .. n] && length xs == n

edgesOfPath :: [Int] -> [(Int, Int)]
edgesOfPath xs = zip xs (drop 1 xs)

validHamiltonianPath :: Graph -> Assignment -> Bool
validHamiltonianPath g@(Graph n _) asn =
  isPermutation n route
    && all (`Set.member` adj) (edgesOfPath route)
  where
    route = decodeHamiltonian n asn
    adj = adjacency g

validHamiltonianCycle :: Graph -> Assignment -> Bool
validHamiltonianCycle g@(Graph n _) asn =
  isPermutation n route
    && all (`Set.member` adj) (edgesOfPath route)
    && (n < 2 || closesCycle)
  where
    route = decodeHamiltonian n asn
    adj = adjacency g
    closesCycle = case route of
      (first : _) -> Set.member (last route, first) adj
      []          -> False
