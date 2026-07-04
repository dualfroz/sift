module Sift.Tseitin
  ( TseitinResult(..)
  , tseitin
  ) where

import Sift.Types
import Sift.Formula
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data TseitinResult = TseitinResult
  { tsCnf     :: CNF
  , tsNameVar :: Map Name Var
  , tsTop     :: Var
  } deriving (Eq, Show)

data St = St
  { stNext    :: Int
  , stNames   :: Map Name Var
  , stClauses :: [Clause]
  }

tseitin :: Formula -> TseitinResult
tseitin formula =
  let (top, st) = encode formula (St 1 Map.empty [])
      full = [posLit top] : stClauses st
  in TseitinResult (CNF full) (stNames st) top

fresh :: St -> (Var, St)
fresh st = (Var (stNext st), st { stNext = stNext st + 1 })

atomVar :: Name -> St -> (Var, St)
atomVar name st =
  case Map.lookup name (stNames st) of
    Just v  -> (v, st)
    Nothing ->
      let (v, st') = fresh st
      in (v, st' { stNames = Map.insert name v (stNames st') })

emit :: [Clause] -> St -> St
emit cs st = st { stClauses = cs ++ stClauses st }

encode :: Formula -> St -> (Var, St)
encode (Atom n) st = atomVar n st
encode (Const b) st =
  let (g, st1) = fresh st
      unit = if b then [posLit g] else [negLit g]
  in (g, emit [unit] st1)
encode (Not a) st =
  let (ga, st1) = encode a st
      (g, st2)  = fresh st1
      cls = [ [negLit g, negLit ga]
            , [posLit g, posLit ga] ]
  in (g, emit cls st2)
encode (And a b) st =
  let (ga, st1) = encode a st
      (gb, st2) = encode b st1
      (g, st3)  = fresh st2
      cls = [ [negLit g, posLit ga]
            , [negLit g, posLit gb]
            , [posLit g, negLit ga, negLit gb] ]
  in (g, emit cls st3)
encode (Or a b) st =
  let (ga, st1) = encode a st
      (gb, st2) = encode b st1
      (g, st3)  = fresh st2
      cls = [ [posLit g, negLit ga]
            , [posLit g, negLit gb]
            , [negLit g, posLit ga, posLit gb] ]
  in (g, emit cls st3)
encode (Imp a b) st =
  let (ga, st1) = encode a st
      (gb, st2) = encode b st1
      (g, st3)  = fresh st2
      cls = [ [negLit g, negLit ga, posLit gb]
            , [posLit g, posLit ga]
            , [posLit g, negLit gb] ]
  in (g, emit cls st3)
encode (Iff a b) st =
  let (ga, st1) = encode a st
      (gb, st2) = encode b st1
      (g, st3)  = fresh st2
      cls = [ [negLit g, negLit ga, posLit gb]
            , [negLit g, posLit ga, negLit gb]
            , [posLit g, posLit ga, posLit gb]
            , [posLit g, negLit ga, negLit gb] ]
  in (g, emit cls st3)
