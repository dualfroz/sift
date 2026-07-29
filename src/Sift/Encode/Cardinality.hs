module Sift.Encode.Cardinality
  ( atLeastOne
  , atMostOne
  , exactlyOne
  , atMostK
  , atLeastK
  , exactlyK
  ) where

import Sift.Types

atLeastOne :: [Lit] -> [Clause]
atLeastOne lits = [lits]

atMostOne :: [Lit] -> [Clause]
atMostOne lits =
  [ [neg a, neg b]
  | (a, rest) <- pairsFrom lits
  , b <- rest
  ]

exactlyOne :: [Lit] -> [Clause]
exactlyOne lits = atLeastOne lits ++ atMostOne lits

pairsFrom :: [a] -> [(a, [a])]
pairsFrom []       = []
pairsFrom (x : xs) = (x, xs) : pairsFrom xs

atMostK :: Int -> [Lit] -> Int -> ([Clause], Int)
atMostK k lits freshStart
  | k <= 0    = (map (\l -> [neg l]) lits, freshStart)
  | n <= k    = ([], freshStart)
  | otherwise = (concat (zipWith rowClauses [1 ..] lits), freshStart + n * k)
  where
    n = length lits
    reg i j = posLit (Var (freshStart + (i - 1) * k + (j - 1)))
    rowClauses i xi
      | i == 1 =
          [ [neg xi, reg 1 1] ]
          ++ [ [neg (reg 1 j)] | j <- [2 .. k] ]
      | i == n =
          [ [neg xi, neg (reg (i - 1) k)] ]
      | otherwise =
          [ [neg xi, reg i 1]
          , [neg (reg (i - 1) 1), reg i 1] ]
          ++ concat
               [ [ [neg xi, neg (reg (i - 1) (j - 1)), reg i j]
                 , [neg (reg (i - 1) j), reg i j] ]
               | j <- [2 .. k] ]
          ++ [ [neg xi, neg (reg (i - 1) k)] ]

atLeastK :: Int -> [Lit] -> Int -> ([Clause], Int)
atLeastK k lits = atMostK (n - k) (map neg lits)
  where n = length lits

exactlyK :: Int -> [Lit] -> Int -> ([Clause], Int)
exactlyK k lits freshStart =
  let (atMost, fresh1) = atMostK k lits freshStart
      (atLeast, fresh2) = atLeastK k lits fresh1
  in (atMost ++ atLeast, fresh2)
