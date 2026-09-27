module Main (main) where

import Sift.Types
import Sift.Dimacs (parseDimacs, renderDimacs)
import Sift.Formula
import Sift.Tseitin
import Sift.Solver (Result(..), solve)
import Sift.Verify (satisfies, completeModel)
import Sift.Pigeonhole (pigeonhole)
import Sift.Cdcl (CdclResult(..), solveCdcl, lubySequence)
import Sift.Cdcl.Heap
import Sift.Preprocess
import Sift.Preprocess.Bve
import Sift.Encode.Cardinality
import Sift.Encode.Queens
import Sift.Encode.Coloring
import Sift.Encode.Sudoku
import Sift.Encode.VertexCover
import Sift.Encode.Hamiltonian
import Sift.Theory.DiffLogic
import Sift.Xor
import Sift.Enumerate
import Sift.Cdcl.Incremental
import Sift.Proof.Drat

import Control.Monad.ST (ST, runST)
import Data.Array.ST
import Data.Bits ((.&.))
import Data.List (sort, nub, permutations)
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import System.Exit (exitFailure, exitSuccess)

main :: IO ()
main = do
  let randCnfSatCount = length (filter (isSat . solve) randomCnfs)
  putStrLn ("Random CNF corpus: " ++ show (length randomCnfs)
            ++ " formulas, " ++ show randCnfSatCount ++ " SAT / "
            ++ show (length randomCnfs - randCnfSatCount) ++ " UNSAT (by DPLL)")
  putStrLn "---"
  outcomes <- sequence tests
  let total  = length outcomes
      passed = length (filter id outcomes)
  putStrLn "---"
  putStrLn (show passed ++ "/" ++ show total ++ " tests passed")
  if passed == total then exitSuccess else exitFailure

tests :: [IO Bool]
tests =
  [ check "(a v b) ^ (~a) is SAT" (isSat (solve cnfSatSmall))
  , check "  and its model satisfies every clause" (modelVerifies cnfSatSmall)
  , check "  model forces a=False" (fst forcedSmall)
  , check "  model forces b=True" (snd forcedSmall)
  , check "(a) ^ (~a) is UNSAT" (solve cnfUnsatSmall == Unsat)
  , check "empty clause makes formula UNSAT" (solve (CNF [[]]) == Unsat)
  , check "empty CNF is trivially SAT" (isSat (solve (CNF [])))

  , check "PHP(4,3) pigeonhole is UNSAT" (solve (pigeonhole 4 3) == Unsat)
  , check "PHP(3,2) pigeonhole is UNSAT" (solve (pigeonhole 3 2) == Unsat)
  , check "PHP(5,4) pigeonhole is UNSAT" (solve (pigeonhole 5 4) == Unsat)
  , check "PHP(3,3) is SAT with a verified model" (modelVerifies (pigeonhole 3 3))
  , check "PHP(4,4) is SAT with a verified model" (modelVerifies (pigeonhole 4 4))

  , check ("DPLL agrees with brute force on " ++ show (length randomCnfs) ++ " random CNFs")
          (all agreesWithBruteForce randomCnfs)
  , check "every SAT verdict from DPLL comes with a verified model"
          (all satVerdictVerified randomCnfs)
  , check ("solver finds a verified model for " ++ show (length satisfiableCnfs)
           ++ " constructed-satisfiable CNFs")
          (all constructedModelVerifies satisfiableCnfs)

  , check "Tseitin equisat: (a & ~a) is UNSAT both ways" (equisatFixed "a & ~a" False)
  , check "Tseitin equisat: (a | ~a) is SAT both ways" (equisatFixed "a | ~a" True)
  , check "Tseitin equisat: (a -> b) & a & ~b is UNSAT" (equisatFixed "(a -> b) & a & ~b" False)
  , check "Tseitin equisat: chain of iff with a<->~c is UNSAT"
          (equisatFixed "(a <-> b) & (b <-> c) & (a <-> ~c)" False)
  , check "Tseitin equisat: (a|b)&(~a|c)&(~b|~c) is SAT" (equisatFixed "(a | b) & (~a | c) & (~b | ~c)" True)
  , check ("Tseitin equisat vs brute force on " ++ show (length randomFormulas) ++ " random formulas")
          (all tseitinEquisat randomFormulas)
  , check "extracted Tseitin model always evaluates the formula to True"
          (all tseitinModelSound randomFormulas)

  , check "DIMACS round trip on a fixed sample" dimacsRoundTripFixed
  , check ("DIMACS round trip on " ++ show (length randomCnfs) ++ " random CNFs")
          (all dimacsRoundTrip randomCnfs)
  , check "parsing and solving the fixed DIMACS sample yields a verified model"
          dimacsParseSolveVerify

  , check "formula parser evaluates a & (b | ~c) correctly" parserEvaluates
  , check "formula parser respects precedence (~ then & then ->)" parserPrecedence

  , check "Luby sequence prefix matches reference" lubyPrefixOk
  , check "Luby is always a power of two" (all isPowerOfTwo (lubySequence 200))

  , check ("CDCL agrees with brute force on " ++ show (length randomCnfs) ++ " random CNFs")
          (all cdclCorrect randomCnfs)
  , check ("CDCL agrees with DPLL on " ++ show (length randomCnfs) ++ " random CNFs")
          (all cdclMatchesDpll randomCnfs)
  , check ("CDCL finds a verified model for " ++ show (length satisfiableCnfs)
           ++ " constructed-satisfiable CNFs")
          (all cdclModelVerifies satisfiableCnfs)
  , check "CDCL: empty clause is UNSAT" (solveCdcl (CNF [[]]) == CdclUnsat)
  , check "CDCL: empty CNF is SAT" (isCdclSat (solveCdcl (CNF [])))
  , check "CDCL: (a v b) ^ (~a) forces a=False, b=True" cdclForcedSmall
  , check ("CDCL solves Tseitin CNFs equisat to brute force on "
           ++ show (length randomFormulas) ++ " formulas")
          (all cdclTseitinEquisat randomFormulas)

  , check "CDCL: PHP(3,2) is UNSAT" (solveCdcl (pigeonhole 3 2) == CdclUnsat)
  , check "CDCL: PHP(4,3) is UNSAT" (solveCdcl (pigeonhole 4 3) == CdclUnsat)
  , check "CDCL: PHP(5,4) is UNSAT" (solveCdcl (pigeonhole 5 4) == CdclUnsat)
  , check "CDCL: PHP(6,5) is UNSAT" (solveCdcl (pigeonhole 6 5) == CdclUnsat)
  , check "CDCL: PHP(7,6) is UNSAT" (solveCdcl (pigeonhole 7 6) == CdclUnsat)
  , check "CDCL: PHP(5,5) is SAT with a verified model" (cdclModelVerifies (pigeonhole 5 5))

  , check "at-most-one encodes cardinality <= 1 exactly" (all atMostOneCorrect [1 .. 5])
  , check "exactly-one encodes cardinality == 1 exactly" (all exactlyOneCorrect [1 .. 5])
  , check "at-least-one is a single clause of all literals" atLeastOneShape

  , check "queens N=1 is SAT" (isCdclSat (solveCdcl (queens 1)))
  , check "queens N=2 is UNSAT" (solveCdcl (queens 2) == CdclUnsat)
  , check "queens N=3 is UNSAT" (solveCdcl (queens 3) == CdclUnsat)
  , check "queens N=4..10 are SAT with valid placements"
          (all queensSatValid [4 .. 10])

  , check "coloring: K4 needs 4 colors (3 is UNSAT)"
          (solveCdcl (coloring 3 completeK4) == CdclUnsat)
  , check "coloring: K4 is 4-colorable with a valid coloring"
          (coloringSatValid 4 completeK4)
  , check "coloring: odd cycle C5 is not 2-colorable"
          (solveCdcl (coloring 2 cycleC5) == CdclUnsat)
  , check "coloring: odd cycle C5 is 3-colorable with a valid coloring"
          (coloringSatValid 3 cycleC5)
  , check "coloring: even cycle C6 is 2-colorable with a valid coloring"
          (coloringSatValid 2 cycleC6)
  , check "coloring: bipartite graph is 2-colorable with a valid coloring"
          (coloringSatValid 2 bipartite)

  , check "sudoku: a real puzzle is solved with a valid grid"
          (sudokuSolvesValid sudokuPuzzle)
  , check "sudoku: two identical givens in a row make it UNSAT"
          (solveCdcl (sudoku 3 [(1, 1, 5), (1, 2, 5)]) == CdclUnsat)

  , check "preprocess: subsumption preserves the model set on random CNFs"
          (all (\c -> modelSetEq c (subsume c)) randomCnfs)
  , check "preprocess: self-subsuming resolution preserves the model set"
          (all (\c -> modelSetEq c (selfSubsume c)) randomCnfs)
  , check "preprocess: unit propagation is equisatisfiable and sound"
          (all unitPropSound randomCnfs)
  , check "preprocess: pure literal elimination is equisatisfiable"
          (all pureElimEquisat randomCnfs)
  , check ("preprocess: full pipeline is correct on " ++ show (length randomCnfs)
           ++ " random CNFs")
          (all preprocessCorrect randomCnfs)

  , check "difference logic: a negative cycle is UNSAT" (solveDl dlNegCycle == DlUnsat)
  , check "difference logic: a feasible system is SAT with a verified model"
          (dlSatVerified dlFeasible)
  , check "difference logic: disjunctive constraint picks a feasible branch"
          (dlSatVerified dlDisjunctive)
  , check ("difference logic agrees with bounded brute force on "
           ++ show (length randomDlProblems) ++ " random problems")
          (all dlAgrees randomDlProblems)

  , check "at-most-k (sequential counter) encodes <= k exactly"
          (all (\n -> all (cardCorrect atMostK (<=) n) [0 .. n]) [1 .. 4])
  , check "at-least-k (sequential counter) encodes >= k exactly"
          (all (\n -> all (cardCorrect atLeastK (>=) n) [0 .. n]) [1 .. 4])
  , check "exactly-k (sequential counter) encodes == k exactly"
          (all (\n -> all (cardCorrect exactlyK (==) n) [0 .. n]) [1 .. 4])

  , check "vertex cover: triangle K3 has a cover of size 2 but not 1"
          (vcSatValid 2 triangleK3 && solveCdcl (vertexCover 1 triangleK3) == CdclUnsat)
  , check "vertex cover: odd cycle C5 needs 3, not 2"
          (vcSatValid 3 cycleC5 && solveCdcl (vertexCover 2 cycleC5) == CdclUnsat)
  , check "vertex cover: star K1,3 is covered by its center alone"
          (vcSatValid 1 star13)

  , check ("BVE is equisatisfiable and reconstructs models on "
           ++ show (length randomCnfs) ++ " random CNFs")
          (all bveCorrect randomCnfs)
  , check ("BVE reconstructs models for " ++ show (length satisfiableCnfs)
           ++ " constructed-satisfiable CNFs")
          (all bveReconstructs satisfiableCnfs)

  , check ("XOR Gaussian solve agrees with brute force on " ++ show (length xorSystems)
           ++ " random GF(2) systems")
          (all xorGaussSound xorSystems)
  , check "XOR Gaussian solve is equisatisfiable to the CNF expansion"
          (all xorEquisat xorSystems)
  , check "XOR empty parity-1 clause is UNSAT, parity-0 is SAT"
          (gaussIsUnsat (xorClause [] True) && gaussIsSat (xorClause [] False))

  , check "hamiltonian path agrees with brute-force permutation search"
          (all hamPathOk hamGraphs)
  , check "hamiltonian cycle agrees with brute-force permutation search"
          (all hamCycleOk hamGraphs)

  , check ("model enumeration counts match brute force on " ++ show (length randomCnfs)
           ++ " random CNFs")
          (all enumerateOk randomCnfs)
  , check "N-queens solution counts match the known sequence for N=1..7"
          queensCountsOk

  , check ("incremental SAT under assumptions agrees with brute force on "
           ++ show (length incAssumps) ++ " cases")
          (all incrementalOk incAssumps)
  , check "incremental final conflict clause is a real unsatisfiable core"
          (all incrementalCoreReal incAssumps)
  , check "batched incremental queries reuse the solver without changing verdicts"
          incrementalBatchConsistent

  , check ("DRAT/RUP proof or model is correct on " ++ show (length randomCnfs)
           ++ " random CNFs")
          (all dratVerifies randomCnfs)
  , check "DRAT proofs for pigeonhole UNSAT instances verify by RUP"
          phpProofsVerify
  , check "corrupting a pigeonhole proof makes the RUP checker reject it"
          dratCorruptRejected

  , check "heap returns variables in non-increasing activity order"
          (all heapDescends heapActivityCases)
  , check "heap increase-key promotes a bumped variable to the top" heapBumpOk
  ]

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn ((if ok then "PASS  " else "FAIL  ") ++ name)
  return ok

isSat :: Result -> Bool
isSat (Sat _) = True
isSat Unsat   = False

modelVerifies :: CNF -> Bool
modelVerifies cnf = case solve cnf of
  Sat model -> satisfies model cnf
  Unsat     -> False

cnfSatSmall :: CNF
cnfSatSmall = CNF [ [posLit (Var 1), posLit (Var 2)]
                  , [negLit (Var 1)] ]

cnfUnsatSmall :: CNF
cnfUnsatSmall = CNF [ [posLit (Var 1)]
                    , [negLit (Var 1)] ]

forcedSmall :: (Bool, Bool)
forcedSmall = case solve cnfSatSmall of
  Sat model -> ( Map.lookup (Var 1) model == Just False
               , Map.lookup (Var 2) model == Just True )
  Unsat     -> (False, False)

bruteForceSat :: CNF -> Bool
bruteForceSat cnf = any (`satisfies` cnf) (allAssignments (allVars cnf))

allAssignments :: [Var] -> [Assignment]
allAssignments []       = [Map.empty]
allAssignments (v : vs) = [ Map.insert v b m | b <- [False, True], m <- allAssignments vs ]

agreesWithBruteForce :: CNF -> Bool
agreesWithBruteForce cnf = case solve cnf of
  Sat _  -> bruteForceSat cnf
  Unsat  -> not (bruteForceSat cnf)

satVerdictVerified :: CNF -> Bool
satVerdictVerified cnf = case solve cnf of
  Sat model -> satisfies model cnf
  Unsat     -> True

constructedModelVerifies :: CNF -> Bool
constructedModelVerifies cnf = case solve cnf of
  Sat model -> satisfies model cnf
  Unsat     -> False

allEnvs :: [Name] -> [Map Name Bool]
allEnvs []       = [Map.empty]
allEnvs (n : ns) = [ Map.insert n b e | b <- [False, True], e <- allEnvs ns ]

formulaSat :: Formula -> Bool
formulaSat f = any (`evalFormula` f) (allEnvs (atoms f))

tseitinSat :: Formula -> Bool
tseitinSat = isSat . solve . tsCnf . tseitin

tseitinModel :: Formula -> Maybe (Map Name Bool)
tseitinModel f =
  let result = tseitin f
  in case solve (tsCnf result) of
       Sat asn -> Just (Map.fromList
                    [ (name, Map.findWithDefault True v asn)
                    | (name, v) <- Map.toList (tsNameVar result) ])
       Unsat   -> Nothing

equisatFixed :: String -> Bool -> Bool
equisatFixed src expected = case parseFormula src of
  Left _  -> False
  Right f -> formulaSat f == expected
             && tseitinSat f == expected
             && formulaSat f == tseitinSat f

tseitinEquisat :: Formula -> Bool
tseitinEquisat f = formulaSat f == tseitinSat f

tseitinModelSound :: Formula -> Bool
tseitinModelSound f = case tseitinModel f of
  Just env -> evalFormula env f
  Nothing  -> not (formulaSat f)

sampleDimacs :: String
sampleDimacs = unlines
  [ "c a fixed sample"
  , "c second comment line"
  , "p cnf 3 3"
  , "1 -2 0"
  , "2 3 0"
  , "-1 -3 0" ]

dimacsRoundTripFixed :: Bool
dimacsRoundTripFixed = case parseDimacs sampleDimacs of
  Left _     -> False
  Right cnf1 -> parseDimacs (renderDimacs cnf1) == Right cnf1

dimacsRoundTrip :: CNF -> Bool
dimacsRoundTrip cnf = parseDimacs (renderDimacs cnf) == Right cnf

dimacsParseSolveVerify :: Bool
dimacsParseSolveVerify = case parseDimacs sampleDimacs of
  Left _    -> False
  Right cnf -> case solve cnf of
    Sat model -> satisfies model cnf
    Unsat     -> False

parserEvaluates :: Bool
parserEvaluates = case parseFormula "a & (b | ~c)" of
  Left _  -> False
  Right f ->
       evalFormula (env [("a", True), ("b", False), ("c", False)]) f
    && not (evalFormula (env [("a", True), ("b", False), ("c", True)]) f)
    && not (evalFormula (env [("a", False), ("b", True), ("c", True)]) f)
  where env = Map.fromList

parserPrecedence :: Bool
parserPrecedence =
  parseFormula "~a & b -> c"
    == Right (Imp (And (Not (Atom "a")) (Atom "b")) (Atom "c"))

type Seed = Int

nextRand :: Seed -> (Int, Seed)
nextRand s = let s' = (1103515245 * s + 12345) .&. 0x7fffffff in (s', s')

randInt :: Int -> Int -> Seed -> (Int, Seed)
randInt lo hi s = let (v, s') = nextRand s in (lo + v `mod` (hi - lo + 1), s')

randBool :: Seed -> (Bool, Seed)
randBool s = let (v, s') = nextRand s in (even v, s')

genN :: Int -> (Seed -> (a, Seed)) -> Seed -> ([a], Seed)
genN 0 _ s = ([], s)
genN k g s = let (x, s')   = g s
                 (xs, s'') = genN (k - 1) g s'
             in (x : xs, s'')

randLit :: Int -> Seed -> (Lit, Seed)
randLit numVars s0 =
  let (v, s1) = randInt 1 numVars s0
      (b, s2) = randBool s1
  in (Lit (Var v) b, s2)

randClause :: Int -> Int -> Seed -> (Clause, Seed)
randClause numVars maxLen s0 =
  let (len, s1) = randInt 1 maxLen s0
  in genN len (randLit numVars) s1

randCnf :: Seed -> (CNF, Seed)
randCnf s0 =
  let (nc, s1)  = randInt 1 8 s0
      (cls, s2) = genN nc (randClause 5 3) s1
  in (CNF cls, s2)

randomCnfs :: [CNF]
randomCnfs = fst (genN 200 randCnf 12345)

randAssignment :: Int -> Seed -> (Assignment, Seed)
randAssignment n = go n Map.empty
  where
    go 0 acc s = (acc, s)
    go k acc s = let (b, s') = randBool s
                 in go (k - 1) (Map.insert (Var k) b acc) s'

satClause :: Int -> Assignment -> Seed -> (Clause, Seed)
satClause numVars target s0 =
  let (v, s1)      = randInt 1 numVars s0
      trueLit      = Lit (Var v) (target Map.! Var v)
      (extra, s2)  = randInt 0 2 s1
      (extras, s3) = genN extra (randLit numVars) s2
  in (trueLit : extras, s3)

genSatisfiable :: Seed -> (CNF, Seed)
genSatisfiable s0 =
  let numVars      = 6
      (target, s1) = randAssignment numVars s0
      (nc, s2)     = randInt 1 10 s1
      (cls, s3)    = genN nc (satClause numVars target) s2
  in (CNF cls, s3)

satisfiableCnfs :: [CNF]
satisfiableCnfs = fst (genN 200 genSatisfiable 999)

atomPool :: [Name]
atomPool = ["a", "b", "c", "d"]

randFormula :: Int -> Seed -> (Formula, Seed)
randFormula depth s0
  | depth <= 0 = randLeaf s0
  | otherwise =
      let (choice, s1) = randInt 0 6 s0
      in case choice of
           1 -> let (a, s2) = randFormula (depth - 1) s1 in (Not a, s2)
           2 -> bin And (depth - 1) s1
           3 -> bin Or  (depth - 1) s1
           4 -> bin Imp (depth - 1) s1
           5 -> bin Iff (depth - 1) s1
           _ -> randLeaf s1
  where
    bin con d s = let (a, s')  = randFormula d s
                      (b, s'') = randFormula d s'
                  in (con a b, s'')

randLeaf :: Seed -> (Formula, Seed)
randLeaf s0 = let (k, s1) = randInt 0 (length atomPool - 1) s0
              in (Atom (atomPool !! k), s1)

randomFormulas :: [Formula]
randomFormulas = fst (genN 200 (randFormula 3) 4242)

isCdclSat :: CdclResult -> Bool
isCdclSat (CdclSat _) = True
isCdclSat CdclUnsat   = False

lubyPrefixOk :: Bool
lubyPrefixOk =
  lubySequence 15 == [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]

isPowerOfTwo :: Int -> Bool
isPowerOfTwo n = n > 0 && (n .&. (n - 1)) == 0

cdclCorrect :: CNF -> Bool
cdclCorrect cnf = case solveCdcl cnf of
  CdclSat model -> satisfies model cnf && bruteForceSat cnf
  CdclUnsat     -> not (bruteForceSat cnf)

cdclMatchesDpll :: CNF -> Bool
cdclMatchesDpll cnf = isCdclSat (solveCdcl cnf) == isSat (solve cnf)

cdclModelVerifies :: CNF -> Bool
cdclModelVerifies cnf = case solveCdcl cnf of
  CdclSat model -> satisfies model cnf
  CdclUnsat     -> False

cdclForcedSmall :: Bool
cdclForcedSmall = case solveCdcl cnfSatSmall of
  CdclSat model -> Map.lookup (Var 1) model == Just False
                && Map.lookup (Var 2) model == Just True
  CdclUnsat     -> False

cdclTseitinEquisat :: Formula -> Bool
cdclTseitinEquisat f = isCdclSat (solveCdcl (tsCnf (tseitin f))) == formulaSat f

countTrue :: Int -> Assignment -> Int
countTrue n asn = length [ () | i <- [1 .. n], Map.findWithDefault False (Var i) asn ]

atMostOneCorrect :: Int -> Bool
atMostOneCorrect n =
  all (\asn -> satisfies asn cnf == (countTrue n asn <= 1)) (allAssignments vs)
  where
    lits = [ posLit (Var i) | i <- [1 .. n] ]
    cnf  = CNF (atMostOne lits)
    vs   = [ Var i | i <- [1 .. n] ]

exactlyOneCorrect :: Int -> Bool
exactlyOneCorrect n =
  all (\asn -> satisfies asn cnf == (countTrue n asn == 1)) (allAssignments vs)
  where
    lits = [ posLit (Var i) | i <- [1 .. n] ]
    cnf  = CNF (exactlyOne lits)
    vs   = [ Var i | i <- [1 .. n] ]

atLeastOneShape :: Bool
atLeastOneShape = atLeastOne lits == [lits]
  where lits = [ posLit (Var 1), posLit (Var 2), posLit (Var 3) ]

queensSatValid :: Int -> Bool
queensSatValid n = case solveCdcl (queens n) of
  CdclSat model -> validQueens n model
  CdclUnsat     -> False

coloringSatValid :: Int -> Graph -> Bool
coloringSatValid k g = case solveCdcl (coloring k g) of
  CdclSat model -> validColoring k g model
  CdclUnsat     -> False

completeK4 :: Graph
completeK4 = Graph 4 [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

cycleC5 :: Graph
cycleC5 = Graph 5 [(1, 2), (2, 3), (3, 4), (4, 5), (5, 1)]

cycleC6 :: Graph
cycleC6 = Graph 6 [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 1)]

bipartite :: Graph
bipartite = Graph 6 [(1, 4), (1, 5), (2, 5), (2, 6), (3, 4), (3, 6)]

sudokuSolvesValid :: [(Int, Int, Int)] -> Bool
sudokuSolvesValid givens = case solveCdcl (sudoku 3 givens) of
  CdclSat model -> validSudoku 3 givens model
  CdclUnsat     -> False

sudokuPuzzle :: [(Int, Int, Int)]
sudokuPuzzle = parseGrid 3 (unlines
  [ "530070000"
  , "600195000"
  , "098000060"
  , "800060003"
  , "400803001"
  , "700020006"
  , "060000280"
  , "000419005"
  , "000080079" ])

modelSetEq :: CNF -> CNF -> Bool
modelSetEq a b =
  all (\asn -> satisfies asn a == satisfies asn b) (allAssignments vs)
  where vs = nub (allVars a ++ allVars b)

unitPropSound :: CNF -> Bool
unitPropSound cnf = case unitPropagate cnf of
  Nothing -> not (bruteForceSat cnf)
  Just (units, residual) ->
    bruteForceSat cnf == bruteForceSat residual
      && case solveCdcl residual of
           CdclSat m -> satisfies (completeModel cnf (reconstruct units m)) cnf
           CdclUnsat -> True

pureElimEquisat :: CNF -> Bool
pureElimEquisat cnf =
  bruteForceSat cnf == bruteForceSat residual
    && case solveCdcl residual of
         CdclSat m -> satisfies (completeModel cnf (reconstruct pures m)) cnf
         CdclUnsat -> True
  where (pures, residual) = pureLiteralElim cnf

preprocessCorrect :: CNF -> Bool
preprocessCorrect cnf = case preprocess cnf of
  Unsatisfiable -> not (bruteForceSat cnf)
  Simplified fixed residual ->
    bruteForceSat cnf == bruteForceSat residual
      && case solveCdcl residual of
           CdclSat m -> satisfies (completeModel cnf (reconstruct fixed m)) cnf
           CdclUnsat -> True

dlNegCycle :: DlProblem
dlNegCycle = DlProblem
  [DiffAtom 1 2 0, DiffAtom 2 3 0, DiffAtom 3 1 (-1)]
  (CNF [[posLit (Var 1)], [posLit (Var 2)], [posLit (Var 3)]])

dlFeasible :: DlProblem
dlFeasible = DlProblem
  [DiffAtom 1 2 2, DiffAtom 2 3 3]
  (CNF [[posLit (Var 1)], [posLit (Var 2)]])

dlDisjunctive :: DlProblem
dlDisjunctive = DlProblem
  [DiffAtom 1 2 (-1), DiffAtom 2 1 (-1)]
  (CNF [[posLit (Var 1), posLit (Var 2)]])

dlSatVerified :: DlProblem -> Bool
dlSatVerified prob = case solveDl prob of
  DlSat model -> dlModelSatisfies prob model
  DlUnsat     -> False

dlAgrees :: DlProblem -> Bool
dlAgrees prob =
  let brute = dlBruteSat prob
  in case solveDl prob of
       DlSat model -> brute && dlModelSatisfies prob model
       DlUnsat     -> not brute

dlBruteSat :: DlProblem -> Bool
dlBruteSat prob =
  any (\assignment -> dlModelSatisfies prob (Map.fromList assignment)) (intAssignments vars)
  where vars = nub (concatMap (\a -> [dlLhs a, dlRhs a]) (dlAtoms prob))

intAssignments :: [Int] -> [[(Int, Int)]]
intAssignments = go
  where
    domain = [-6 .. 6]
    go []       = [[]]
    go (v : vs) = [ (v, d) : rest | d <- domain, rest <- go vs ]

randDlAtom :: Int -> Seed -> (DiffAtom, Seed)
randDlAtom numDlVars s0 =
  let (a, s1) = randInt 1 numDlVars s0
      (b, s2) = randInt 1 numDlVars s1
      (w, s3) = randInt (-2) 2 s2
  in (DiffAtom a b w, s3)

randDlLit :: Int -> Seed -> (Lit, Seed)
randDlLit numAtoms s0 =
  let (v, s1) = randInt 1 numAtoms s0
      (b, s2) = randBool s1
  in (Lit (Var v) b, s2)

randDlClause :: Int -> Seed -> (Clause, Seed)
randDlClause numAtoms s0 =
  let (len, s1) = randInt 1 2 s0
  in genN len (randDlLit numAtoms) s1

randDlProblem :: Seed -> (DlProblem, Seed)
randDlProblem s0 =
  let numAtoms  = 4
      numDlVars = 3
      (as, s1)  = genN numAtoms (randDlAtom numDlVars) s0
      (nc, s2)  = randInt 1 5 s1
      (cls, s3) = genN nc (randDlClause numAtoms) s2
  in (DlProblem as (CNF cls), s3)

randomDlProblems :: [DlProblem]
randomDlProblems = fst (genN 60 randDlProblem 20240828)

buildDoubleArray :: [Double] -> ST s (STUArray s Int Double)
buildDoubleArray xs = newListArray (0, length xs - 1) xs

zeroDoubleArray :: Int -> ST s (STUArray s Int Double)
zeroDoubleArray n = newArray (0, n - 1) 0

popAll :: VarHeap s -> ST s [Int]
popAll h = do
  done <- heapIsEmpty h
  if done
    then return []
    else do
      v <- heapRemoveMax h
      rest <- popAll h
      return (v : rest)

nonIncreasing :: [Double] -> Bool
nonIncreasing xs = and (zipWith (>=) xs (drop 1 xs))

heapDescends :: [Double] -> Bool
heapDescends acts = runST $ do
  let n = length acts
  arr <- buildDoubleArray acts
  h <- newHeap n arr
  mapM_ (heapInsert h) [0 .. n - 1]
  popped <- popAll h
  let poppedActs = map (acts !!) popped
  return (nonIncreasing poppedActs
          && sort poppedActs == sort acts
          && length popped == n)

heapActivityCases :: [[Double]]
heapActivityCases =
  [ [3, 1, 4, 1, 5, 9, 2, 6]
  , [1, 2, 3, 4, 5]
  , [5, 4, 3, 2, 1]
  , [2, 2, 2, 2]
  , [7]
  , [0.5, 10.5, 3.3, 3.3, 8.1, 0.0]
  ]

heapBumpOk :: Bool
heapBumpOk = runST $ do
  arr <- zeroDoubleArray 5
  h <- newHeap 5 arr
  mapM_ (heapInsert h) [0 .. 4]
  writeArray arr 3 100
  heapIncrease h 3
  top <- heapRemoveMax h
  return (top == 3)

bitVectors :: Int -> [[Bool]]
bitVectors 0 = [[]]
bitVectors m = [ b : rest | b <- [False, True], rest <- bitVectors (m - 1) ]

cardCorrect :: (Int -> [Lit] -> Int -> ([Clause], Int)) -> (Int -> Int -> Bool) -> Int -> Int -> Bool
cardCorrect enc predicate n k = all matchesCount (bitVectors n)
  where
    lits = [ posLit (Var i) | i <- [1 .. n] ]
    matchesCount bits =
      let units = zipWith (\i b -> [ if b then posLit (Var i) else negLit (Var i) ]) [1 ..] bits
          (cardClauses, _) = enc k lits (n + 1)
      in isCdclSat (solveCdcl (CNF (cardClauses ++ units)))
           == predicate (length (filter id bits)) k

vcSatValid :: Int -> Graph -> Bool
vcSatValid k g = case solveCdcl (vertexCover k g) of
  CdclSat model -> validVertexCover k g model
  CdclUnsat     -> False

triangleK3 :: Graph
triangleK3 = Graph 3 [(1, 2), (2, 3), (1, 3)]

star13 :: Graph
star13 = Graph 4 [(1, 2), (1, 3), (1, 4)]

bveCorrect :: CNF -> Bool
bveCorrect cnf =
  bruteForceSat cnf == bruteForceSat (bveCnf r)
    && case solveCdcl (bveCnf r) of
         CdclSat m -> satisfies (completeModel cnf (reconstructBve r m)) cnf
         CdclUnsat -> True
  where r = bve cnf

bveReconstructs :: CNF -> Bool
bveReconstructs cnf = case solveCdcl (bveCnf r) of
  CdclSat m -> satisfies (completeModel cnf (reconstructBve r m)) cnf
  CdclUnsat -> not (bruteForceSat cnf)
  where r = bve cnf

randXorClause :: Int -> Seed -> (XorClause, Seed)
randXorClause numVars s0 =
  let (parity, s1) = randBool s0
      pick v st = let (b, st') = randBool st in (if b then [Var v] else [], st')
      go []       st acc = (acc, st)
      go (v : rest) st acc = let (xs, st') = pick v st in go rest st' (acc ++ xs)
      (vs, s2) = go [1 .. numVars] s1 []
  in (xorClause vs parity, s2)

randXorSystem :: Seed -> ([XorClause], Seed)
randXorSystem s0 = let (nc, s1) = randInt 1 6 s0 in genN nc (randXorClause 5) s1

xorSystems :: [[XorClause]]
xorSystems = fst (genN 200 randXorSystem 777)

xorBruteSat :: [XorClause] -> Bool
xorBruteSat sys = any (`systemSatisfies` sys) (allAssignments vs)
  where vs = nub [ Var v | c <- sys, v <- IntSet.toList (xorVars c) ]

gaussIsSat :: XorClause -> Bool
gaussIsSat c = case gaussSolve [c] of Just _ -> True; Nothing -> False

gaussIsUnsat :: XorClause -> Bool
gaussIsUnsat = not . gaussIsSat

xorGaussSound :: [XorClause] -> Bool
xorGaussSound sys = case gaussSolve sys of
  Just m  -> systemSatisfies m sys && xorBruteSat sys
  Nothing -> not (xorBruteSat sys)

xorEquisat :: [XorClause] -> Bool
xorEquisat sys =
  isGaussSat == isCdclSat (solveCdcl (systemToCnf sys))
  where isGaussSat = case gaussSolve sys of Just _ -> True; Nothing -> False

hamGraphs :: [Graph]
hamGraphs =
  [ Graph 4 [(1, 2), (2, 3), (3, 4)]
  , Graph 4 [(1, 2), (2, 3), (3, 4), (4, 1)]
  , Graph 5 [(1, 2), (2, 3), (3, 4), (4, 5), (5, 1)]
  , Graph 4 [(1, 2), (1, 3), (1, 4)]
  , Graph 5 [(1, 2), (2, 3), (3, 1), (3, 4), (4, 5)]
  , Graph 6 [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 1), (1, 4)]
  ]

adjPairs :: Graph -> [(Int, Int)]
adjPairs (Graph _ edges) = concat [ [(u, w), (w, u)] | (u, w) <- edges ]

brutePathExists :: Graph -> Bool
brutePathExists g@(Graph n _) = any ok (permutations [1 .. n])
  where
    adj = adjPairs g
    ok p = all (`elem` adj) (zip p (drop 1 p))

bruteCycleExists :: Graph -> Bool
bruteCycleExists g@(Graph n _) = any ok (permutations [1 .. n])
  where
    adj = adjPairs g
    ok p = all (`elem` adj) (zip p (drop 1 p))
             && (n < 2 || closes p)
    closes p = case p of
      (first : _) -> (last p, first) `elem` adj
      []          -> False

hamPathOk :: Graph -> Bool
hamPathOk g = case solveCdcl (hamiltonianPath g) of
  CdclSat m -> validHamiltonianPath g m && brutePathExists g
  CdclUnsat -> not (brutePathExists g)

hamCycleOk :: Graph -> Bool
hamCycleOk g = case solveCdcl (hamiltonianCycle g) of
  CdclSat m -> validHamiltonianCycle g m && bruteCycleExists g
  CdclUnsat -> not (bruteCycleExists g)

countBrute :: CNF -> Int
countBrute cnf = length (filter (`satisfies` cnf) (allAssignments (allVars cnf)))

enumerateOk :: CNF -> Bool
enumerateOk cnf = countModels (allVars cnf) cnf == countBrute cnf

queensCountsOk :: Bool
queensCountsOk = [ countQueensSolutions n | n <- [1 .. 7] ] == [1, 0, 0, 2, 10, 4, 40]

randAssumpSet :: Int -> Seed -> ([Lit], Seed)
randAssumpSet numVars s0 = let (k, s1) = randInt 0 3 s0 in genN k (randLit numVars) s1

incAssumps :: [(CNF, [Lit])]
incAssumps =
  concat
    [ let (sets, _) = genN 3 (randAssumpSet 5) (9000 + i)
      in [ (cnf, a) | a <- sets ]
    | (i, cnf) <- zip [0 ..] randomCnfs ]

bruteIncSat :: CNF -> [Lit] -> Bool
bruteIncSat cnf assumps = any ok (allAssignments vs)
  where
    vs = nub (allVars cnf ++ map litVar assumps)
    ok m = satisfies m cnf && all (\l -> litValue m l == Just True) assumps

incrementalOk :: (CNF, [Lit]) -> Bool
incrementalOk (cnf, assumps) = case solveAssuming cnf assumps of
  IncSat m       -> satisfies m cnf
                      && all (\l -> litValue m l == Just True) assumps
                      && bruteIncSat cnf assumps
  IncUnsat _core -> not (bruteIncSat cnf assumps)

incrementalCoreReal :: (CNF, [Lit]) -> Bool
incrementalCoreReal (cnf, assumps) = case solveAssuming cnf assumps of
  IncSat _       -> True
  IncUnsat core  -> all (`elem` assumps) core && not (bruteIncSat cnf core)

incrementalBatchConsistent :: Bool
incrementalBatchConsistent =
  all consistent (take 40 (groupQueries incAssumps))
  where
    groupQueries pairs = [ (cnf, [ a | (c, a) <- pairs, c == cnf ]) | cnf <- nub (map fst pairs) ]
    consistent (cnf, queries) =
      let batched = solveManyAssuming cnf queries
      in length batched == length queries
           && map isIncSat batched == map (isIncSat . solveAssuming cnf) queries
           && and (zipWith (validResult cnf) batched queries)
    isIncSat (IncSat _)   = True
    isIncSat (IncUnsat _) = False
    validResult cnf (IncSat m) as =
      satisfies m cnf && all (\l -> litValue m l == Just True) as
    validResult cnf (IncUnsat core) as =
      all (`elem` as) core && not (bruteIncSat cnf core)

dratVerifies :: CNF -> Bool
dratVerifies cnf = case solveProof cnf of
  ProofSat m   -> satisfies m cnf
  ProofUnsat p -> not (bruteForceSat cnf) && verifyProof cnf p

phpProofsVerify :: Bool
phpProofsVerify = all ok [(3, 2), (4, 3), (5, 4)]
  where
    ok (h, p) = case solveProof (pigeonhole h p) of
      ProofUnsat proof -> verifyProof (pigeonhole h p) proof
      ProofSat _       -> False

dratCorruptRejected :: Bool
dratCorruptRejected = all rejected [pigeonhole 4 3, pigeonhole 5 4]
  where
    rejected cnf = case solveProof cnf of
      ProofUnsat proof -> length proof >= 2 && not (verifyProof cnf (drop 1 proof))
      ProofSat _       -> False
