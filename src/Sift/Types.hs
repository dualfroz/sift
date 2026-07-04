module Sift.Types
  ( Var(..)
  , varId
  , Lit(..)
  , posLit
  , negLit
  , neg
  , litFromInt
  , litToInt
  , Clause
  , CNF(..)
  , Assignment
  , litValue
  , varsOfClause
  , allVars
  ) where

import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

newtype Var = Var Int
  deriving (Eq, Ord)

instance Show Var where
  show (Var n) = 'x' : show n

varId :: Var -> Int
varId (Var n) = n

data Lit = Lit
  { litVar  :: Var
  , litSign :: Bool
  } deriving (Eq, Ord)

instance Show Lit where
  show (Lit (Var n) s) = (if s then "" else "-") ++ show n

posLit :: Var -> Lit
posLit v = Lit v True

negLit :: Var -> Lit
negLit v = Lit v False

neg :: Lit -> Lit
neg (Lit v s) = Lit v (not s)

litFromInt :: Int -> Lit
litFromInt n
  | n > 0     = Lit (Var n) True
  | n < 0     = Lit (Var (negate n)) False
  | otherwise = error "litFromInt: 0 is a clause terminator, not a literal"

litToInt :: Lit -> Int
litToInt (Lit (Var n) s) = if s then n else negate n

type Clause = [Lit]

newtype CNF = CNF { clauses :: [Clause] }
  deriving (Eq, Show)

type Assignment = Map Var Bool

litValue :: Assignment -> Lit -> Maybe Bool
litValue asn (Lit v s) = fmap (== s) (Map.lookup v asn)

varsOfClause :: Clause -> [Var]
varsOfClause = nub . map litVar

allVars :: CNF -> [Var]
allVars (CNF cs) = nub (concatMap (map litVar) cs)
