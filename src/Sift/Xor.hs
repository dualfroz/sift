module Sift.Xor
  ( XorClause(..)
  , xorClause
  , xorVarsOf
  , xorSatisfies
  , systemSatisfies
  , xorToCnf
  , systemToCnf
  , GaussResult(..)
  , gauss
  , gaussSolve
  ) where

import Sift.Types
import Data.List (sortOn)
import qualified Data.Foldable as Foldable
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Map.Strict as Map

data XorClause = XorClause
  { xorVars   :: IntSet
  , xorParity :: Bool
  } deriving (Eq, Ord, Show)

xorClause :: [Var] -> Bool -> XorClause
xorClause vs parity =
  let raw = map varId vs
      folded = Foldable.foldl' (\acc v -> if IntSet.member v acc
                                            then IntSet.delete v acc
                                            else IntSet.insert v acc)
                               IntSet.empty raw
  in XorClause folded parity

xorVarsOf :: XorClause -> [Var]
xorVarsOf = map Var . IntSet.toList . xorVars

xorSatisfies :: Assignment -> XorClause -> Bool
xorSatisfies asn (XorClause vs parity) =
  IntSet.foldr (\v acc -> acc /= Map.findWithDefault False (Var v) asn) False vs == parity

systemSatisfies :: Assignment -> [XorClause] -> Bool
systemSatisfies asn = all (xorSatisfies asn)

xorToCnf :: XorClause -> [Clause]
xorToCnf (XorClause vs parity) =
  [ clauseFor signs
  | signs <- assignmentsOver n
  , violates signs ]
  where
    varList = map Var (IntSet.toList vs)
    n = length varList
    violates signs = odd (length (filter id signs)) /= parity
    clauseFor signs =
      [ if s then negLit v else posLit v
      | (v, s) <- zip varList signs ]

assignmentsOver :: Int -> [[Bool]]
assignmentsOver 0 = [[]]
assignmentsOver k = [ b : rest | b <- [False, True], rest <- assignmentsOver (k - 1) ]

systemToCnf :: [XorClause] -> CNF
systemToCnf = CNF . concatMap xorToCnf

data Row = Row
  { rowVars :: IntSet
  , rowRhs  :: Bool
  } deriving (Eq, Show)

xorRows :: Row -> Row -> Row
xorRows a b = Row (symDiff (rowVars a) (rowVars b)) (rowRhs a /= rowRhs b)

symDiff :: IntSet -> IntSet -> IntSet
symDiff a b = IntSet.union (IntSet.difference a b) (IntSet.difference b a)

data GaussResult
  = GaussUnsat
  | GaussSat [(Int, Row)]
  deriving (Eq, Show)

gauss :: [XorClause] -> GaussResult
gauss system = go [] (map toRow system)
  where
    toRow (XorClause vs parity) = Row vs parity
    go pivots [] = GaussSat pivots
    go pivots (r : rest) =
      let reduced = reduce pivots r
      in if IntSet.null (rowVars reduced)
           then if rowRhs reduced then GaussUnsat else go pivots rest
           else
             let pivotVar = IntSet.findMin (rowVars reduced)
                 pivots'  = insertPivot pivotVar reduced pivots
             in go pivots' rest

reduce :: [(Int, Row)] -> Row -> Row
reduce pivots row =
  Foldable.foldl' (\acc (pv, prow) ->
                     if IntSet.member pv (rowVars acc) then xorRows acc prow else acc)
                  row
                  (sortOn fst pivots)

insertPivot :: Int -> Row -> [(Int, Row)] -> [(Int, Row)]
insertPivot pivotVar row pivots =
  (pivotVar, row) : map back pivots
  where
    back (pv, prow) =
      if IntSet.member pivotVar (rowVars prow)
        then (pv, xorRows prow row)
        else (pv, prow)

gaussSolve :: [XorClause] -> Maybe Assignment
gaussSolve system =
  case gauss system of
    GaussUnsat      -> Nothing
    GaussSat pivots ->
      let allVarsSet = IntSet.unions (map xorVars system)
          pivotVars  = IntSet.fromList (map fst pivots)
          freeVars   = IntSet.difference allVarsSet pivotVars
          base       = Map.fromList [ (Var v, False) | v <- IntSet.toList freeVars ]
          solved     = Foldable.foldl' assignPivot base pivots
      in Just solved
  where
    assignPivot acc (pv, row) =
      let others = IntSet.delete pv (rowVars row)
          othersXor = IntSet.foldr (\v a -> a /= Map.findWithDefault False (Var v) acc) False others
          val = othersXor /= rowRhs row
      in Map.insert (Var pv) val acc
