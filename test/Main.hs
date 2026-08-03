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
