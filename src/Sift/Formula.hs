module Sift.Formula
  ( Name
  , Formula(..)
  , atoms
  , evalFormula
  , parseFormula
  ) where

import Data.Char (isAlpha, isAlphaNum, isSpace)
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

type Name = String

data Formula
  = Atom Name
  | Const Bool
  | Not Formula
  | And Formula Formula
  | Or  Formula Formula
  | Imp Formula Formula
  | Iff Formula Formula
  deriving (Eq, Show)

atoms :: Formula -> [Name]
atoms = nub . collect
  where
    collect (Atom n)  = [n]
    collect (Const _) = []
    collect (Not a)   = collect a
    collect (And a b) = collect a ++ collect b
    collect (Or a b)  = collect a ++ collect b
    collect (Imp a b) = collect a ++ collect b
    collect (Iff a b) = collect a ++ collect b

evalFormula :: Map Name Bool -> Formula -> Bool
evalFormula env = go
  where
    go (Atom n)  = fromMaybe (error ("unbound atom: " ++ n)) (Map.lookup n env)
    go (Const b) = b
    go (Not a)   = not (go a)
    go (And a b) = go a && go b
    go (Or a b)  = go a || go b
    go (Imp a b) = not (go a) || go b
    go (Iff a b) = go a == go b

data Token
  = TLParen
  | TRParen
  | TNot
  | TAnd
  | TOr
  | TImp
  | TIff
  | TTrue
  | TFalse
  | TName Name
  deriving (Eq, Show)

tokenize :: String -> Either String [Token]
tokenize [] = Right []
tokenize (c : cs)
  | isSpace c = tokenize cs
  | c == '('  = (TLParen :) <$> tokenize cs
  | c == ')'  = (TRParen :) <$> tokenize cs
  | c == '~'  = (TNot :) <$> tokenize cs
  | c == '!'  = (TNot :) <$> tokenize cs
  | c == '&'  = (TAnd :) <$> tokenize cs
  | c == '|'  = (TOr :) <$> tokenize cs
  | c == '-', ('>' : rest) <- cs = (TImp :) <$> tokenize rest
  | c == '=', ('>' : rest) <- cs = (TImp :) <$> tokenize rest
  | c == '<', ('-' : '>' : rest) <- cs = (TIff :) <$> tokenize rest
  | c == '<', ('=' : '>' : rest) <- cs = (TIff :) <$> tokenize rest
  | isAlpha c =
      let (word, rest) = span isIdentChar (c : cs)
      in (keyword word :) <$> tokenize rest
  | otherwise = Left ("unexpected character: " ++ show c)

isIdentChar :: Char -> Bool
isIdentChar ch = isAlphaNum ch || ch == '_'

keyword :: String -> Token
keyword word = case word of
  "true"  -> TTrue
  "false" -> TFalse
  "not"   -> TNot
  "and"   -> TAnd
  "or"    -> TOr
  _       -> TName word

parseFormula :: String -> Either String Formula
parseFormula src = do
  toks <- tokenize src
  (formula, rest) <- pIff toks
  case rest of
    [] -> Right formula
    _  -> Left ("unexpected trailing tokens: " ++ show rest)

type Parse = [Token] -> Either String (Formula, [Token])

pIff :: Parse
pIff ts = do
  (left, r1) <- pImp ts
  chain left r1
  where
    chain left (TIff : rest) = do
      (right, r2) <- pImp rest
      chain (Iff left right) r2
    chain left rest = Right (left, rest)

pImp :: Parse
pImp ts = do
  (left, r1) <- pOr ts
  case r1 of
    (TImp : rest) -> do
      (right, r2) <- pImp rest
      Right (Imp left right, r2)
    _ -> Right (left, r1)

pOr :: Parse
pOr ts = do
  (left, r1) <- pAnd ts
  chain left r1
  where
    chain left (TOr : rest) = do
      (right, r2) <- pAnd rest
      chain (Or left right) r2
    chain left rest = Right (left, rest)

pAnd :: Parse
pAnd ts = do
  (left, r1) <- pNot ts
  chain left r1
  where
    chain left (TAnd : rest) = do
      (right, r2) <- pNot rest
      chain (And left right) r2
    chain left rest = Right (left, rest)

pNot :: Parse
pNot (TNot : rest) = do
  (formula, r) <- pNot rest
  Right (Not formula, r)
pNot ts = pAtom ts

pAtom :: Parse
pAtom (TLParen : rest) = do
  (formula, r1) <- pIff rest
  case r1 of
    (TRParen : r2) -> Right (formula, r2)
    _              -> Left "expected closing parenthesis"
pAtom (TTrue : rest)   = Right (Const True, rest)
pAtom (TFalse : rest)  = Right (Const False, rest)
pAtom (TName n : rest) = Right (Atom n, rest)
pAtom ts               = Left ("expected atom, got: " ++ show ts)
