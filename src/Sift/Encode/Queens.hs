module Sift.Encode.Queens
  ( queens
  , queensCell
  , decodeQueens
  , validQueens
  ) where

import Sift.Types
import Sift.Encode.Cardinality
import qualified Data.Map.Strict as Map

queensCell :: Int -> Int -> Int -> Var
queensCell n r c = Var ((r - 1) * n + c)

queens :: Int -> CNF
queens n = CNF (rowExactly ++ colAtMost ++ diagAtMost)
  where
    cell r c = posLit (queensCell n r c)
    rowExactly = concat
      [ exactlyOne [ cell r c | c <- [1 .. n] ] | r <- [1 .. n] ]
    colAtMost = concat
      [ atMostOne [ cell r c | r <- [1 .. n] ] | c <- [1 .. n] ]
    diagAtMost = concatMap atMostOne (downDiagonals ++ upDiagonals)
    downDiagonals =
      [ [ cell r c | r <- [1 .. n], c <- [1 .. n], r - c == k ]
      | k <- [negate (n - 1) .. n - 1] ]
    upDiagonals =
      [ [ cell r c | r <- [1 .. n], c <- [1 .. n], r + c == k ]
      | k <- [2 .. 2 * n] ]

decodeQueens :: Int -> Assignment -> [(Int, Int)]
decodeQueens n asn =
  [ (r, c)
  | r <- [1 .. n], c <- [1 .. n]
  , Map.findWithDefault False (queensCell n r c) asn ]

validQueens :: Int -> Assignment -> Bool
validQueens n asn =
  length placed == n
    && distinct (map fst placed)
    && distinct (map snd placed)
    && distinct (map (\(r, c) -> r - c) placed)
    && distinct (map (\(r, c) -> r + c) placed)
  where
    placed = decodeQueens n asn

distinct :: Ord a => [a] -> Bool
distinct xs = length xs == Map.size (Map.fromList (zip xs (repeat ())))
