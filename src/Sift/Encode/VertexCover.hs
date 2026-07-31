module Sift.Encode.VertexCover
  ( vertexCover
  , decodeVertexCover
  , validVertexCover
  ) where

import Sift.Types
import Sift.Encode.Cardinality (atMostK)
import Sift.Encode.Coloring (Graph(..))
import qualified Data.Map.Strict as Map

vertexCover :: Int -> Graph -> CNF
vertexCover k (Graph vertices edges) = CNF (edgeClauses ++ cardClauses)
  where
    inCover v = posLit (Var v)
    edgeClauses = [ [inCover u, inCover w] | (u, w) <- edges ]
    (cardClauses, _) = atMostK k [ inCover v | v <- [1 .. vertices] ] (vertices + 1)

decodeVertexCover :: Int -> Assignment -> [Int]
decodeVertexCover vertices asn =
  [ v | v <- [1 .. vertices], Map.findWithDefault False (Var v) asn ]

validVertexCover :: Int -> Graph -> Assignment -> Bool
validVertexCover k (Graph vertices edges) asn =
  length cover <= k
    && all (\(u, w) -> u `elem` coverSet || w `elem` coverSet) edges
  where
    cover = decodeVertexCover vertices asn
    coverSet = cover
