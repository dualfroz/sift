module Sift.Encode.Sudoku
  ( sudoku
  , sudokuCell
  , decodeSudoku
  , validSudoku
  , parseGrid
  ) where

import Sift.Types
import Sift.Encode.Cardinality
import Data.Char (digitToInt, isDigit)
import Data.List (transpose)
import qualified Data.Map.Strict as Map

sudokuCell :: Int -> Int -> Int -> Int -> Var
sudokuCell n r c d = Var (((r - 1) * n + (c - 1)) * n + d)

sudoku :: Int -> [(Int, Int, Int)] -> CNF
sudoku boxN givens = CNF (cellClauses ++ rowClauses ++ colClauses ++ boxClauses ++ givenClauses)
  where
    n = boxN * boxN
    lit r c d = posLit (sudokuCell n r c d)
    cellClauses = concat
      [ exactlyOne [ lit r c d | d <- [1 .. n] ]
      | r <- [1 .. n], c <- [1 .. n] ]
    rowClauses = concat
      [ exactlyOne [ lit r c d | c <- [1 .. n] ]
      | r <- [1 .. n], d <- [1 .. n] ]
    colClauses = concat
      [ exactlyOne [ lit r c d | r <- [1 .. n] ]
      | c <- [1 .. n], d <- [1 .. n] ]
    boxClauses = concat
      [ exactlyOne [ lit r c d | (r, c) <- boxCells br bc ]
      | br <- [1 .. boxN], bc <- [1 .. boxN], d <- [1 .. n] ]
    boxCells br bc =
      [ ((br - 1) * boxN + i, (bc - 1) * boxN + j)
      | i <- [1 .. boxN], j <- [1 .. boxN] ]
    givenClauses = [ [ lit r c d ] | (r, c, d) <- givens ]

decodeSudoku :: Int -> Assignment -> [[Int]]
decodeSudoku boxN asn =
  [ [ cellDigit r c | c <- [1 .. n] ] | r <- [1 .. n] ]
  where
    n = boxN * boxN
    cellDigit r c =
      case [ d | d <- [1 .. n], Map.findWithDefault False (sudokuCell n r c d) asn ] of
        (d : _) -> d
        []      -> 0

validSudoku :: Int -> [(Int, Int, Int)] -> Assignment -> Bool
validSudoku boxN givens asn =
  all fullPermutation grid
    && all fullPermutation (transpose grid)
    && all fullPermutation boxes
    && all givenHolds givens
  where
    n = boxN * boxN
    grid = decodeSudoku boxN asn
    fullPermutation row = permutationOf n row
    boxes =
      [ [ (grid !! (r - 1)) !! (c - 1)
        | (r, c) <-
            [ ((br - 1) * boxN + i, (bc - 1) * boxN + j)
            | i <- [1 .. boxN], j <- [1 .. boxN] ] ]
      | br <- [1 .. boxN], bc <- [1 .. boxN] ]
    givenHolds (r, c, d) = (grid !! (r - 1)) !! (c - 1) == d

permutationOf :: Int -> [Int] -> Bool
permutationOf n row =
  Map.fromList (zip row (repeat ())) == Map.fromList (zip [1 .. n] (repeat ()))
    && length row == n

parseGrid :: Int -> String -> [(Int, Int, Int)]
parseGrid boxN text =
  [ (r, c, digitToInt ch)
  | (r, line) <- zip [1 ..] rows
  , (c, ch) <- zip [1 ..] line
  , isDigit ch, ch /= '0' ]
  where
    rows = take n (map (take n . padCells) (lines text))
    n = boxN * boxN
    padCells line = line ++ replicate n '0'
