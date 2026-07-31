module Main (main) where

import Sift.Types
import Sift.Dimacs (parseDimacs, renderModel)
import Sift.Solver (Result(..), solve)
import Sift.Cdcl (CdclResult(..), solveCdclStats)
import Sift.Stats (Stats(..), renderStats)
import Sift.Verify (satisfies, completeModel)
import Sift.Preprocess (PreResult(..), preprocess, reconstruct)
import Sift.Proof.Drat (ProofResult(..), solveProof, verifyProof, renderProof)
import Sift.Pigeonhole (pigeonhole)
import Sift.Encode.Queens (queens, validQueens)
import Sift.Encode.Coloring (Graph(..), coloring, validColoring)
import Sift.Encode.Sudoku (sudoku, validSudoku, parseGrid)

import Control.Monad (forM_, when)
import Data.List (isPrefixOf, isSuffixOf, sort)
import System.CPUTime (getCPUTime)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitWith, ExitCode(..))
import System.FilePath ((</>))
import Text.Printf (printf)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("solve" : rest) -> runSolve rest
    ("bench" : rest) -> runBench rest
    _                -> do
      putStrLn "usage:"
      putStrLn "  sift solve <file.cnf> [--dpll] [--pp] [--proof] [--proof-out=<file>]"
      putStrLn "  sift bench [<dir>]"
      exitWith (ExitFailure 2)

runSolve :: [String] -> IO ()
runSolve rawArgs =
  case [ a | a <- rawArgs, take 2 a /= "--" ] of
    [path] -> do
      let useDpll  = "--dpll" `elem` rawArgs
          usePp    = "--pp" `elem` rawArgs
          useProof = "--proof" `elem` rawArgs
          proofOut = lookupFlag "--proof-out=" rawArgs
      contents <- readFile path
      case parseDimacs contents of
        Left err -> do
          putStrLn ("c parse error: " ++ err)
          exitWith (ExitFailure 2)
        Right cnf
          | useProof  -> reportProof cnf proofOut
          | useDpll   -> reportDpll cnf
          | usePp     -> reportPreprocessed cnf
          | otherwise -> reportCdcl cnf
    _ -> do
      putStrLn "usage: sift solve <file.cnf> [--dpll] [--pp] [--proof] [--proof-out=<file>]"
      exitWith (ExitFailure 2)

lookupFlag :: String -> [String] -> Maybe String
lookupFlag prefix args =
  case [ drop (length prefix) a | a <- args, prefix `isPrefixOf` a ] of
    (v : _) -> Just v
    []      -> Nothing

reportProof :: CNF -> Maybe FilePath -> IO ()
reportProof cnf proofOut =
  case solveProof cnf of
    ProofSat model -> emitModel cnf model
    ProofUnsat proof -> do
      putStrLn "s UNSATISFIABLE"
      putStrLn ("c DRAT/RUP proof has " ++ show (length proof) ++ " lemmas (final empty clause included)")
      case proofOut of
        Just file -> do
          writeFile file (renderProof proof)
          putStrLn ("c proof written to " ++ file)
        Nothing -> pure ()
      if verifyProof cnf proof
        then putStrLn "c proof verified: reverse unit propagation refutes the formula"
        else do
          putStrLn "c ERROR: proof failed RUP verification"
          exitFailure

reportCdcl :: CNF -> IO ()
reportCdcl cnf = do
  let (result, st) = solveCdclStats cnf
  mapM_ putStrLn (renderStats st)
  case result of
    CdclUnsat -> putStrLn "s UNSATISFIABLE"
    CdclSat model -> emitModel cnf model

reportDpll :: CNF -> IO ()
reportDpll cnf =
  case solve cnf of
    Unsat     -> putStrLn "s UNSATISFIABLE"
    Sat model -> emitModel cnf model

reportPreprocessed :: CNF -> IO ()
reportPreprocessed cnf =
  case preprocess cnf of
    Unsatisfiable -> putStrLn "s UNSATISFIABLE"
    Simplified fixed residual -> do
      putStrLn ("c preprocessing fixed " ++ show (length fixed) ++ " literals, "
                ++ show (length (clauses residual)) ++ " clauses remain")
      let (result, st) = solveCdclStats residual
      mapM_ putStrLn (renderStats st)
      case result of
        CdclUnsat -> putStrLn "s UNSATISFIABLE"
        CdclSat residualModel -> do
          let full = completeModel cnf (reconstruct fixed residualModel)
          emitModel cnf full

emitModel :: CNF -> Assignment -> IO ()
emitModel cnf model = do
  let full = completeModel cnf model
  putStrLn "s SATISFIABLE"
  putStrLn (renderModel cnf full)
  if satisfies full cnf
    then putStrLn "c model verified against every clause"
    else do
      putStrLn "c ERROR: model does not satisfy the formula"
      exitFailure

runBench :: [String] -> IO ()
runBench args = do
  putStrLn "c sift built-in benchmark suite (CDCL)"
  putStrLn (printf "%-26s %-8s %10s %10s %8s" "instance" "verdict" "conflicts" "props" "ms")
  forM_ benchmarks $ \(name, cnf, checkModel) -> runOne name cnf checkModel
  fileCases <- case args of
    (dir : _) -> loadDir dir
    []        -> loadDir "examples"
  forM_ fileCases $ \(name, cnf) -> runOne name cnf (\m -> satisfies m cnf)
  putStrLn "c all benchmark models verified"

runOne :: String -> CNF -> (Assignment -> Bool) -> IO ()
runOne name cnf checkModel = do
  start <- getCPUTime
  let (result, st) = solveCdclStats cnf
      verdict = case result of CdclSat _ -> "SAT"; CdclUnsat -> "UNSAT"
      ok = case result of
             CdclSat m -> checkModel (completeModel cnf m)
             CdclUnsat -> True
  end <- ok `seq` getCPUTime
  let ms = fromIntegral (end - start) / 1e9 :: Double
  putStrLn (printf "%-26s %-8s %10d %10d %8.1f"
              name verdict (statsConflicts st) (statsPropagations st) ms)
  when (not ok) $ do
    putStrLn ("c ERROR: model for " ++ name ++ " failed verification")
    exitFailure

loadDir :: FilePath -> IO [(String, CNF)]
loadDir dir = do
  exists <- doesDirectoryExist dir
  if not exists
    then pure []
    else do
      entries <- listDirectory dir
      let cnfFiles = sort [ e | e <- entries, ".cnf" `isSuffixOf` e ]
      mapM loadCase cnfFiles
  where
    loadCase file = do
      contents <- readFile (dir </> file)
      case parseDimacs contents of
        Left _    -> pure (file ++ " (parse error)", CNF [])
        Right cnf -> pure (file, cnf)

benchmarks :: [(String, CNF, Assignment -> Bool)]
benchmarks =
  [ ("php(6,5) unsat",     pigeonhole 6 5,             const True)
  , ("php(8,7) unsat",     pigeonhole 8 7,             const True)
  , ("queens-8",           queens 8,                   validQueens 8)
  , ("queens-12",          queens 12,                  validQueens 12)
  , ("queens-20",          queens 20,                  validQueens 20)
  , ("color-k4-3 unsat",   coloring 3 k4,              const True)
  , ("color-k4-4",         coloring 4 k4,              validColoring 4 k4)
  , ("color-petersen-3",   coloring 3 petersen,        validColoring 3 petersen)
  , ("sudoku-easy",        sudoku 3 sudokuGivens,      validSudoku 3 sudokuGivens)
  ]

k4 :: Graph
k4 = Graph 4 [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

petersen :: Graph
petersen = Graph 10
  [ (1,2),(2,3),(3,4),(4,5),(5,1)
  , (6,8),(8,10),(10,7),(7,9),(9,6)
  , (1,6),(2,7),(3,8),(4,9),(5,10) ]

sudokuGivens :: [(Int, Int, Int)]
sudokuGivens = parseGrid 3 (unlines
  [ "530070000"
  , "600195000"
  , "098000060"
  , "800060003"
  , "400803001"
  , "700020006"
  , "060000280"
  , "000419005"
  , "000080079" ])
