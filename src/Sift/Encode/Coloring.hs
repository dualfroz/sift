module Sift.Encode.Coloring
  ( Graph(..)
  , coloring
  , colorCell
  , decodeColoring
  , validColoring
  ) where

import Sift.Types
import Sift.Encode.Cardinality
import qualified Data.Map.Strict as Map

data Graph = Graph
  { graphVertices :: Int
  , graphEdges    :: [(Int, Int)]
  } deriving (Eq, Show)

colorCell :: Int -> Int -> Int -> Var
colorCell colors v c = Var ((v - 1) * colors + c)

coloring :: Int -> Graph -> CNF
coloring colors (Graph vertices edges) = CNF (vertexExactly ++ edgeDistinct)
  where
    cell v c = posLit (colorCell colors v c)
    vertexExactly = concat
      [ exactlyOne [ cell v c | c <- [1 .. colors] ] | v <- [1 .. vertices] ]
    edgeDistinct =
      [ [ neg (cell u c), neg (cell w c) ]
      | (u, w) <- edges, c <- [1 .. colors] ]

decodeColoring :: Int -> Int -> Assignment -> Map.Map Int Int
decodeColoring colors vertices asn = Map.fromList
  [ (v, c)
  | v <- [1 .. vertices]
  , c <- [1 .. colors]
  , Map.findWithDefault False (colorCell colors v c) asn ]

validColoring :: Int -> Graph -> Assignment -> Bool
validColoring colors (Graph vertices edges) asn =
  Map.size assigned == vertices
    && all (\(u, w) -> Map.lookup u assigned /= Map.lookup w assigned) edges
  where
    assigned = decodeColoring colors vertices asn
