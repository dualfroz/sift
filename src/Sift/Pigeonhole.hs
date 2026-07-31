module Sift.Pigeonhole
  ( pigeonhole
  ) where

import Sift.Types

-- pigeonhole pigeons holes encodes: every pigeon sits in some hole, and no two
-- pigeons share a hole. With pigeons > holes the formula is UNSAT.
pigeonhole :: Int -> Int -> CNF
pigeonhole pigeons holes = CNF (atLeastOne ++ atMostOne)
  where
    cell p h = Var ((p - 1) * holes + h)
    atLeastOne =
      [ [ posLit (cell p h) | h <- [1 .. holes] ]
      | p <- [1 .. pigeons] ]
    atMostOne =
      [ [ negLit (cell p h), negLit (cell q h) ]
      | h <- [1 .. holes]
      , p <- [1 .. pigeons]
      , q <- [p + 1 .. pigeons] ]
