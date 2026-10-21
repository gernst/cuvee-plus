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
`-teq -prove -split -prove`. The output options (`-print`, `-z3`,
`-cvc5`, `-verify`, `-o`) apply to the result, wherever they appear.
`./Cuvee.sh -help` lists all options with a short description.

## Input

| Option | Meaning |
|---|---|
| `-arch 32\|64` | the data model of C input, 32 or 64 bit Linux (ILP32 or LP64), e.g. for `sizeof`; by default 64, or the data model of an SV-COMP task |
| `-unbounded` | nondeterministic values of C input are unbounded integers, unsigned ones only nonnegative, instead of within the ranges of their types; unsigned arithmetic does not wrap around |
| `-entry <name>` | the procedure where executions start, which `-teq` and `-chc` check; by default `main` in C, none otherwise (SV-LIB starts at its `verify-call` commands, `-chc` needs an entry point in Dafny, Boogie, and SMT-LIB); `-vcgen` ignores it and checks every procedure against its contract |
| `-include <file>` | inject `<file>` into the input after its prelude, parsed in the language of its extension; `-include teq:<concept>` injects the module `<concept>` of the lemma database of `-teq` (`aggregation`, `arithmetic`, `arrays`, `counters`, `search`, `sorted`, `strides`, `unsigned`); Dafny files can also include others themselves, `include "path"` ([architecture.md](architecture.md)) |
| `-hybrid` | inject the definitions of parallel composition into Dafny input: channels, events, the history, `send`, and `receive` |

## Transformations

| Option | Meaning |
|---|---|
| `-vcgen` | verification conditions for procedures by weakest preconditions: contracts, loops with invariants, termination measures, global variables, nondeterministic choice and iteration |
| `-teq` | verification conditions by symbolic execution, each loop summarized by a Trace Equation System (TEQ): the modified variables of a loop partitioned by the strongly connected components of their read relation, one trace per component, of several accumulators for a cycle, whose per-variable traces are views that `-prove` follows on demand; injects the lemma database `teq.dfy`, whose rules `-prove` applies (see [teq.md](teq.md)) |
| `-chc` | constrained Horn clauses for procedures, for the inference of invariants |
| `-flat` | replace arguments of predicates that are records by their fields, e.g. after `-chc` |
| `-simplify` | contextual simplification of formulas and function definitions, with the rewrite rules of lemmas and axioms with `:rw` (see [simplifier.md](simplifier.md)) |
| `-prove` | the deduction engine of the package `prove`, like `-simplify` for the goals of `-teq`: congruence closure and a simplex as the context, matching modulo the classes and the views of traces of several accumulators, rules over whole cycles (patterns of several accumulators), and forward lemmas (`{:fw}`) (see [prove.md](prove.md)) |
| `-rules` | report the rewrite rules that `-simplify` applies to each assertion, by their names, as `(set-info :used ((name count) ...))` after it |
| `-fallback` | lower the Trace Equation Systems that remain into first-order logic for the solvers, e.g. after `-teq -prove`, a trace of several accumulators into one function per accumulator; the lowered goals are `:abstract` |
| `-split` | split goals and lemmas into individual obligations `forall xs. antecedents ==> conclusion`, which the solvers report one by one |
| `-monomorph` | replace polymorphic functions by their monomorphic instances, e.g. before `-z3` |
| `-fuse` | fuse the compositions of defined functions in the requests `fuse g(f(xs), ys) = ???` of Dafny input |

## Output

| Option | Meaning |
|---|---|
| `-print <lang>` | print the output in `<lang>` instead of the language of the input: `smt2`, `dfy`, `bpl`, `c`, `lean` (the logic only: sorts, datatypes, functions, axioms, lemmas, and goals), `scala` (the internal representation), or `null` (nothing) |
| `-linewidth <n>` | lay out the output for lines of `<n>` characters (default 80) |
| `-known <features>` | omit the declarations with the comma-separated attributes `<features>` from the output, e.g. `dfy,teq` (a C program without the logic of its Dafny source, where `teq` keeps the declarations and lemmas of the lemma database out of the output) |
| `-o <file>` | write the output to `<file>` and the reports to stdout |

## Solvers and answers

| Option | Meaning |
|---|---|
| `-z3`, `-cvc5` | pass the output to the solver, which checks it: goals and lemmas must hold (a goal that does not is an error), assertions and `check-sat` are passed through, the answers to queries are reported; lemmas with the attribute `free` (Dafny lemmas without a body) are assumed |
| `-timeout <ms>` | timeout per solver query in milliseconds (default 1000) |
| `-verify` | instead of the output, answer `correct`, `incorrect`, or `unknown` to each `verify-call` of SV-LIB, or once for other inputs: whether the program satisfies its specification (contracts and loop invariants), aggregated over all obligations, with the solver if there is one; procedures need `-vcgen`, `-teq`, or `-chc` first. A refutation is `incorrect` unless the goal is `:abstract` (a loop without invariant under `-vcgen`, the lowering of `-fallback`) or applies a function declared `:abstract` (the bit operations of C, uninterpreted on integers other than 0 and 1) |
| `-witness <file>` | `-verify`, and write the witness of SV-COMP (format 2.0) for its answer to a C program or to an SV-COMP task whose input is C to `<file>`: for `correct` a correctness witness, an invariant set without invariants, which leaves the proof to the validator; for `incorrect` a violation witness whose single segment is the target, the call of `reach_error` (or `__VERIFIER_error`), which leaves the search for the path to the validator, if the program has exactly one call (the failing assertion is not known); nothing for `unknown` and for other inputs, e.g. SV-LIB (see [ideas/witnesses.md](../ideas/witnesses.md)) |

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
./Cuvee.sh -teq -prove -split -prove -fallback -z3 -verify task.c   # as in SV-COMP
```
