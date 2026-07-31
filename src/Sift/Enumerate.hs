module Sift.Enumerate
  ( projectModel
  , blockingClause
  , allModels
  , countModels
  , countQueensSolutions
  ) where

import Sift.Types
import Sift.Cdcl (CdclResult(..), solveCdcl)
import Sift.Encode.Queens (queens, queensCell)
import qualified Data.Map.Strict as Map

projectModel :: [Var] -> Assignment -> Assignment
projectModel vars model =
  Map.fromList [ (v, Map.findWithDefault False v model) | v <- vars ]

blockingClause :: [Var] -> Assignment -> Clause
blockingClause vars model =
  [ if Map.findWithDefault False v model then negLit v else posLit v | v <- vars ]

allModels :: [Var] -> CNF -> [Assignment]
allModels projVars (CNF cs0) = go cs0
  where
    go cs = case solveCdcl (CNF cs) of
      CdclUnsat -> []
      CdclSat model ->
        let projected = projectModel projVars model
        in projected : go (blockingClause projVars projected : cs)

countModels :: [Var] -> CNF -> Int
countModels projVars = length . allModels projVars

countQueensSolutions :: Int -> Int
countQueensSolutions n =
  countModels boardVars (queens n)
  where
    boardVars = [ queensCell n r c | r <- [1 .. n], c <- [1 .. n] ]
