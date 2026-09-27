# sift

sift is a SAT solver and propositional logic toolkit written in Haskell. Its core is a
conflict-driven clause learning (CDCL) solver running in the `ST` monad, alongside a classic DPLL
solver, a CNF preprocessor, a RUP proof generator with its own checker, and a set of encoders that
turn combinatorial problems (N-queens, graph coloring, Sudoku, vertex cover, Hamiltonian paths,
cardinality constraints) into CNF. It ships as a library and as a command line tool that reads
DIMACS files and verifies every answer it prints.

## Features

### Solvers

- **CDCL** (`Sift.Cdcl`, `Sift.Cdcl.*`): two watched literals with blocker literals, first-UIP
  conflict analysis, local learnt clause minimization, VSIDS variable activity kept in a binary max-heap
  (decay 0.95), phase saving, Luby restarts (unit of 100 conflicts), LBD scoring and learnt clause
  database reduction (triggered at 2000 learnt clauses; clauses with LBD <= 2 and clauses that are
  the reason of a current assignment are kept, the less active half of the rest is dropped, clause
  activity decay 0.999). Search statistics (decisions, conflicts, propagations, restarts, learnt
  and removed clauses) are returned with every result.
- **Incremental solving under assumptions** (`Sift.Cdcl.Incremental`): `solveAssuming` and
  `solveManyAssuming` run a batch of assumption sets on one solver instance, keeping learnt clauses
  between queries. An UNSAT answer carries the subset of assumptions responsible for the conflict.
- **DPLL** (`Sift.Solver`): unit propagation, pure literal elimination and branching on the most
  frequent literal.
- **Model enumeration** (`Sift.Enumerate`): all models projected onto a chosen set of variables,
  found by adding blocking clauses; model counting, including a ready-made N-queens solution counter.

### Proofs and verification

- **RUP proofs** (`Sift.Proof.Drat`): `solveProof` records every learnt clause during CDCL search
  and returns either a model or a refutation ending with the empty clause. `renderProof` writes it
  in DRAT text format (addition lines only), `verifyProof` and `isRup` check it by reverse unit
  propagation against the original formula.
- **Model checking** (`Sift.Verify`): `satisfies` checks an assignment against every clause,
  `completeModel` fills in variables the solver never assigned.

### Preprocessing

- **Simplification pipeline** (`Sift.Preprocess`): unit propagation, pure literal elimination,
  subsumption and self-subsuming resolution, repeated until nothing changes. `reconstruct` turns a
  model of the simplified formula into a model of the original one.
- **Bounded variable elimination** (`Sift.Preprocess.Bve`): eliminates a variable by resolution
  when the non-tautological resolvents are no more numerous than the clauses they replace;
  `reconstructBve` restores values of eliminated variables.

### Encodings

- **Cardinality** (`Sift.Encode.Cardinality`): at-least-one, pairwise at-most-one, exactly-one,
  and sequential counter encodings of at-most-k, at-least-k and exactly-k with explicit allocation
  of auxiliary variables.
- **Problems**, each with a decoder and an independent validity check of the decoded answer:
  N-queens (`Sift.Encode.Queens`), graph k-coloring (`Sift.Encode.Coloring`), Sudoku of any box
  size with a parser for digit grids (`Sift.Encode.Sudoku`), vertex cover of size k
  (`Sift.Encode.VertexCover`), Hamiltonian path and cycle (`Sift.Encode.Hamiltonian`) and the
  pigeonhole principle (`Sift.Pigeonhole`).

### Logic and theories

- **Propositional formulas** (`Sift.Formula`): a formula type, an evaluator and a parser.
  Operators from highest to lowest precedence: `~`, `!` or `not`; `&` or `and`; `|` or `or`;
  `->` or `=>` (right associative); `<->` or `<=>`. Constants `true` and `false`, parentheses, and
  identifiers made of letters, digits and `_` starting with a letter.
- **Tseitin transformation** (`Sift.Tseitin`): equisatisfiable CNF for any formula, with the mapping
  from atom names to variables and the top-level gate variable.
- **XOR constraints** (`Sift.Xor`): parity constraints over GF(2), solved directly by Gauss-Jordan
  elimination (`gauss`, `gaussSolve`) or expanded into plain CNF (`xorToCnf`, `systemToCnf`).
- **Difference logic** (`Sift.Theory.DiffLogic`): integer constraints of the form `x - y <= c`
  attached to boolean variables of a CNF. The CDCL solver proposes a boolean model, Bellman-Ford
  checks the asserted constraints, and each negative cycle comes back as a blocking clause over
  the atoms on that cycle.

### Input and output

- **DIMACS** (`Sift.Dimacs`): parser for `p cnf` files (comment lines, optional header, `%`
  terminator) and printers for formulas and `v ... 0` model lines.

## Build and run

Requirements: GHC 9.6 to 9.10 and cabal-install 3.10 or newer. The library depends only on `base`,
`containers` and `array`.

```
cabal build
cabal run sift -- solve examples/sat.cnf
```

### Command line

```
sift solve <file.cnf> [--dpll] [--pp] [--proof] [--proof-out=<file>]
sift bench [<dir>]
```

`sift solve` reads a DIMACS file and prints the verdict in the usual `s` / `v` / `c` line format.
A model is always checked against every clause before it is printed.

| Option | Effect |
|---|---|
| (none) | CDCL search, prints search statistics |
| `--pp` | runs the preprocessing pipeline first, then CDCL on the residual formula |
| `--dpll` | uses the DPLL solver instead of CDCL |
| `--proof` | CDCL with proof logging; on UNSAT checks the proof by RUP |
| `--proof-out=<file>` | with `--proof`, also writes the proof to a file |

When several solver options are given, `--proof` wins over `--dpll`, which wins over `--pp`.

```
$ sift solve examples/php43.cnf --proof --proof-out=php43.drat
s UNSATISFIABLE
c DRAT/RUP proof has 6 lemmas (final empty clause included)
c proof written to php43.drat
c proof verified: reverse unit propagation refutes the formula
```

Exit status is 0 for both SAT and UNSAT, 2 for a usage or parse error, and 1 if a model or proof
fails its own verification.

`sift bench` solves a built-in suite with CDCL (pigeonhole, N-queens up to 20, K4 and Petersen
graph coloring, a Sudoku puzzle) followed by every `.cnf` file in `<dir>`, `./examples` by default.
It prints conflicts, propagations and CPU time per instance and validates every model it finds.

### Examples

`examples/` holds the DIMACS instances that `sift bench` loads by default:

| File | Instance |
|---|---|
| `sat.cnf` | four-clause satisfiable formula over three variables |
| `unsat.cnf` | `x1` and `not x1`, unsatisfiable |
| `php43.cnf` | pigeonhole PHP(4,3), unsatisfiable |
| `php65.cnf` | pigeonhole PHP(6,5), unsatisfiable |
| `queens8.cnf` | 8-queens placement, satisfiable |
| `coloring-petersen3.cnf` | 3-coloring of the Petersen graph, satisfiable |

## Tests

```
cabal test
```

The suite in `test/Main.hs` runs 89 checks. Most of them compare a component with an independent
oracle on deterministically generated inputs: CDCL, DPLL, preprocessing, BVE, model enumeration and
incremental solving against brute-force search over all assignments, the Tseitin encoding against
direct evaluation, Gaussian elimination against brute force over GF(2), difference logic against a
bounded integer search, cardinality encodings against counting, and Hamiltonian encodings against
permutation search. It also checks known results (pigeonhole UNSAT, N-queens solution counts for
N = 1..7, chromatic numbers of small graphs), DIMACS round trips, the Luby sequence, the activity
heap, and that the RUP checker rejects a corrupted proof.

## Project layout

```
app/Main.hs                    command line tool (solve, bench)
src/Sift/Types.hs              variables, literals, clauses, CNF, assignments
src/Sift/Dimacs.hs             DIMACS parser and printers
src/Sift/Formula.hs            formula type, evaluator, parser
src/Sift/Tseitin.hs            Tseitin transformation
src/Sift/Solver.hs             DPLL solver
src/Sift/Cdcl.hs               CDCL entry points
src/Sift/Cdcl/State.hs         solver state, clause store, trail, watches
src/Sift/Cdcl/Search.hs        propagation, conflict analysis, restarts, clause reduction
src/Sift/Cdcl/Heap.hs          VSIDS activity heap
src/Sift/Cdcl/Incremental.hs   solving under assumptions
src/Sift/Proof/Drat.hs         proof logging, RUP checker, proof printer
src/Sift/Preprocess.hs         simplification pipeline
src/Sift/Preprocess/Bve.hs     bounded variable elimination
src/Sift/Encode/*.hs           cardinality and problem encoders
src/Sift/Pigeonhole.hs         pigeonhole formulas
src/Sift/Theory/DiffLogic.hs   difference logic on top of CDCL
src/Sift/Xor.hs                XOR constraints and Gaussian elimination
src/Sift/Enumerate.hs          model enumeration and counting
src/Sift/Stats.hs              search statistics
src/Sift/Verify.hs             model checking
test/Main.hs                   test suite
examples/                      DIMACS instances
```

## Limitations

- sift is not tuned to compete with industrial solvers: watch lists are Haskell lists, there is no
  inprocessing during search, and the CLI has no time or conflict limits.
- The DIMACS parser reads the whole file as a `String` and ignores the variable and clause counts
  in the header.
- Proofs contain only clause additions (no deletion lines, no RAT steps). The built-in checker
  runs naive unit propagation per lemma, which is fine for small and medium instances only.
- The preprocessor and BVE work on lists of sets with quadratic passes, and BVE runs a single pass
  over the variables.
- XOR to CNF expansion is exponential in the length of each XOR constraint.
- Difference logic uses integer semantics and stops after an iteration limit, reporting
  `DlUnsat` if that limit is reached.
- Bounded variable elimination, XOR reasoning, difference logic, model enumeration and incremental
  solving are available only through the library, not the command line tool.
- In `sift bench`, a file that fails to parse is listed with a `(parse error)` suffix and solved as
  an empty formula instead of stopping the run.

## License

MIT, see [LICENSE](LICENSE).
