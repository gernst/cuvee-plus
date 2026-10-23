# Command line options

```sh
./Cuvee.sh [options] file
```

The language of the input is given by the extension of `file`: `.smt2`
(SMT-LIB), `.svlib` (SV-LIB), `.bpl` (Boogie), `.dfy` (Dafny), `.c` and `.i`
(C), `.yml` (SV-COMP task definition, whose single input file is C or SV-LIB).
Without options, the input is printed in its own language after parsing and
type checking.

The transformations are applied in the order in which they are given, e.g.
`-teq -prove -split -prove`. The output options (`-print`, `-quiet`,
`-z3`, `-cvc5`, `-o`) apply to the result, wherever they appear.
`./Cuvee.sh -help` lists all options with a short description.

## Input

| Option | Meaning |
|---|---|
| `-arch 32\|64` | the data model of C input, 32 or 64 bit Linux (ILP32 or LP64), e.g. for `sizeof`; by default 64, or the data model of an SV-COMP task |
| `-unbounded` | nondeterministic values of C input are unbounded integers, unsigned ones only nonnegative, instead of within the ranges of their types; unsigned arithmetic does not wrap around |
| `-entry <name>` | the procedure where executions start, which `-teq` and `-chc` check; by default `main` in C, none otherwise (SV-LIB starts at its `verify-call` commands, `-chc` needs an entry point in Dafny, Boogie, and SMT-LIB); `-vcgen` ignores it and checks every procedure against its contract |
| `-include <file>` | inject `<file>` into the input after its prelude, parsed in the language of its extension; `-include <feature>:<name>` injects the module `resources/cuvee/<feature>/<name>.dfy` of a feature (`Config.features`), after the entry modules of the known features: `teq:<concept>` a module of the lemma database of `-teq` (`aggregation`, `arithmetic`, `arrays`, `counters`, `search`, `sorted`, `strides`, `unsigned`), which needs `-teq` or `-known teq`, `implement:<name>` the implementations of `-implement`, which need nothing, after their entry `implement.dfy` (the counter `ticks` and the oracle `nondet`); Dafny files can also include others themselves, `include "path"` ([architecture.md](architecture.md)) |
| `-hybrid` | inject the definitions of parallel composition into Dafny input: channels, events, the history, `send`, and `receive` |

## Transformations

| Option | Meaning |
|---|---|
| `-implement` | replace the functions that functions and methods with the attribute `{:implement pattern}` implement, e.g. those of a module of `-include implement:<name>`: the pattern is the implemented function applied to a permutation of all inputs of the implementation (`x in this` for a member `member(x)` of a datatype `set`). An implementation by a function replaces each application, with the arguments at the positions of the pattern, everywhere except in the implementations: in programs, contracts, invariants, function bodies, axioms, and lemmas. An implementation by a method, whose single output is the result and which may choose it nondeterministically, replaces the applications in the expressions that programs execute by calls, in the order of evaluation, whose results are fresh locals `test`: the right operands of `&&`, `\|\|`, `==>` and the branches of `ite` become conditionals, a loop whose guard has applications becomes an iteration that makes the calls and breaks if the guard is false, whose invariants hold at the beginning of each iteration, before the calls; applications in specifications, under binders, and under `old` are errors. Without it, a translation keeps the task as written, together with the implementations; put it before `-vcgen`, `-teq`, `-chc` |
| `-vcgen` | verification conditions for procedures by weakest preconditions: contracts, loops with invariants, termination measures, global variables, nondeterministic choice and iteration; calls by the contract of the callee, inlined if it has a body and no contract |
| `-teq` | verification conditions by symbolic execution, each loop summarized by a Trace Equation System (TEQ): the modified variables of a loop partitioned by the strongly connected components of their read relation, one trace per component, of several accumulators for a cycle, whose per-variable traces are views that `-prove` follows on demand; injects the lemma database `teq.dfy`, whose rules `-prove` applies (see [teq.md](teq.md)); calls inlined, those of callees with a contract by the contract |
| `-chc` | constrained Horn clauses for procedures, for the inference of invariants |
| `-flat` | replace arguments of predicates that are records by their fields, e.g. after `-chc` |
| `-simplify` | contextual simplification of formulas and function definitions, with the rewrite rules of lemmas and axioms with `:rw` (see [simplifier.md](simplifier.md)) |
| `-prove` | the deduction engine of the package `prove`, like `-simplify` for the goals of `-teq`: congruence closure and a simplex as the context, matching modulo the classes and the views of traces of several accumulators, rules over whole cycles (patterns of several accumulators), and forward lemmas (`{:fw}`) (see [prove.md](prove.md)) |
| `-rules` | report the rewrite rules that `-simplify` applies to each assertion, by their names, as `(set-info :used ((name count) ...))` after it |
| `-fallback` | lower the Trace Equation Systems that remain into first-order logic for the solvers, e.g. after `-teq -prove`, a trace of several accumulators into one function per accumulator; goals and lemmas that are not free are lowered, `:abstract` if they change, polymorphic ones are errors, axioms and free lemmas over traces, lists, and naturals are dropped |
| `-split` | split goals and lemmas into individual obligations `forall xs. antecedents ==> conclusion`, which the solvers report one by one |
| `-monomorph` | replace polymorphic functions by their monomorphic instances, e.g. before `-z3` |
| `-fuse` | fuse the compositions of defined functions in the requests `fuse g(f(xs), ys) = ???` of Dafny input |

## Output

| Option | Meaning |
|---|---|
| `-print <lang>` | print the output in `<lang>` instead of the language of the input: `smt2`, `dfy`, `bpl`, `c`, `lean` (the logic only: sorts, datatypes, functions, axioms, lemmas, and goals), or `scala` (the internal representation) |
| `-quiet` | print no output, only the reports, e.g. the answers to the goals and the errors, which go to stderr (stdout with `-o`) |
| `-linewidth <n>` | lay out the output for lines of `<n>` characters (default 80) |
| `-known <features>` | omit the declarations with the comma-separated attributes `<features>` from the output, e.g. `dfy,teq` (a C program without the logic of its Dafny source, where `teq` keeps the declarations and lemmas of the lemma database out of the output) |
| `-o <file>` | write the output to `<file>` and the reports to stdout |

## Solvers and answers

| Option | Meaning |
|---|---|
| `-z3`, `-cvc5` | pass the output to the solver, which checks it: goals and lemmas that are not free are answered `correct`, `incorrect`, or `unknown` (`unknown` instead of `incorrect` if the goal is `:abstract` or applies a function declared `:abstract`), without solver `correct` for `true`, `incorrect` for `false`, and `unknown` otherwise, combined from the answers to the outputs of a goal (e.g. the parts of `-split`, `correct` if a transform reduced it to `true`); the program is incorrect if one answer is `incorrect` and correct if all are `correct`; `-chc` answers its `check-sat` `correct` for `sat` and `incorrect` for `unsat`; assertions and `check-sat` are passed through, the answers to queries are reported; lemmas with the attribute `free` (Dafny lemmas without a body) are assumed like axioms; procedures need `-vcgen`, `-teq`, or `-chc` first, otherwise they are unsupported and not checked |
| `-timeout <ms>` | timeout per solver query in milliseconds (default 1000) |
| `-witness <file>` | write the witness of SV-COMP (format 2.0) for the verdict of its answers (`incorrect` if one is, `correct` if all are) to a C program or to an SV-COMP task whose input is C to `<file>`: for `correct` a correctness witness, an invariant set without invariants, which leaves the proof to the validator; for `incorrect` a violation witness whose single segment is the target, the call of `reach_error` (or `__VERIFIER_error`), which leaves the search for the path to the validator, if the program has exactly one call (the failing assertion is not known); nothing for `unknown` and for other inputs, e.g. SV-LIB (see [ideas/witnesses.md](../ideas/witnesses.md)) |

## Debugging and tests

| Option | Meaning |
|---|---|
| `-debug <modules>` | print the steps of the given comma-separated modules, e.g. `simplify,rewrite` (the steps of the simplifier and of the rewrite engine that change an expression, in the language of the output, also those of `-prove`, where `rewrite` includes the views of traces of several accumulators, `match` the matches through the definitions of variables and the trace patterns that fail, `conditions` the closed side conditions that fail, `forward` the instances of forward lemmas (`{:fw}`), and `views` the misses of the memo of views, see [prove.md](prove.md)) or `solver` (the communication with the solvers) |
| `-test <file>` | run the example `<file>` with the command line of its first line and compare with the expected `name.out` and `name.err`; with a `.csv` file, check a database of expected results |
| `-help` | list the options |
| `-version` | print the version |

## Examples

```sh
./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/max.dfy              # verify methods
./Cuvee.sh -chc -entry max -z3 examples/dafny/vcgen/max.dfy     # infer invariants
./Cuvee.sh -vcgen -print smt2 examples/dafny/vcgen/max.dfy      # show the goals
./Cuvee.sh -teq examples/dafny/vcgen/sum.dfy                    # Trace Equation Systems
./Cuvee.sh -teq -z3 examples/dafny/vcgen/max.dfy                # loop-free, by symbolic execution
./Cuvee.sh -chc -z3 examples/c/horn/count.c                     # C, invariants by Horn clauses
./Cuvee.sh -teq -prove -split -prove -fallback -z3 task.c   # as in SV-COMP
```
