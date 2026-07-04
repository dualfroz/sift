module Sift.Dimacs
  ( parseDimacs
  , renderDimacs
  , renderModel
  ) where

import Sift.Types
import Data.Char (isSpace)
import Data.List (sortOn)
import qualified Data.Map.Strict as Map

parseDimacs :: String -> Either String CNF
parseDimacs input = do
  let toks = takeWhile (/= "%") (concatMap words (filter (not . isComment) (lines input)))
  body <- case toks of
    ("p" : "cnf" : _ : _ : rest) -> Right rest
    ("p" : _)                    -> Left "malformed header, expected: p cnf <vars> <clauses>"
    _                            -> Right toks
  ints <- traverse readInt body
  Right (CNF (splitOnZero ints))

isComment :: String -> Bool
isComment line = case dropWhile isSpace line of
  ('c' : _) -> True
  []        -> True
  _         -> False

readInt :: String -> Either String Int
readInt s = case reads s of
  [(n, "")] -> Right n
  _         -> Left ("not an integer: " ++ show s)

splitOnZero :: [Int] -> [Clause]
splitOnZero [] = []
splitOnZero xs =
  let (front, rest) = break (== 0) xs
      clause = map litFromInt front
  in case rest of
       (0 : more) -> clause : splitOnZero more
       _          -> [clause | not (null clause)]

renderDimacs :: CNF -> String
renderDimacs (CNF cs) = unlines (header : map renderClause cs)
  where
    maxVar = maximum (0 : map varId (concatMap varsOfClause cs))
    header = "p cnf " ++ show maxVar ++ " " ++ show (length cs)
    renderClause c = unwords (map (show . litToInt) c ++ ["0"])

renderModel :: CNF -> Assignment -> String
renderModel cnf model =
  "v " ++ unwords (map (show . signedLit) orderedVars) ++ " 0"
  where
    orderedVars = sortOn varId (allVars cnf)
    signedLit v =
      let value = Map.findWithDefault True v model
      in if value then varId v else negate (varId v)
