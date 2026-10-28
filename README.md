# Cuvée

Cuvée is a pipeline for program verification in Scala 3. It reads SMT-LIB,
SV-LIB, Boogie, Dafny, and C, translates them into one common representation
of logic and programs, transforms that representation, and prints it in any of
these languages or passes it to an SMT solver (z3 or cvc5). Its verifier for C
and SV-LIB, based on Trace Equation Systems (TEQs), takes part in SV-COMP 2027
(see [SV-COMP](#sv-comp) below).

Main features:

- **Inputs:** SMT-LIB, SV-LIB, Boogie, Dafny, C, and SV-COMP task
  definitions, parsed into one core of logic and programs; **outputs** in any
  of these languages and the logic in Lean 4 (`-print`).
- **Verification conditions** by weakest preconditions (`-vcgen`), **Trace
  Equation Systems** with a database of lemmas, most of them proved in Lean
  (`-teq`), and **constrained Horn clauses** (`-chc`).
- **Deduction engine** (`-prove`) for the goals of trace equation systems, with
  congruence closure, a simplex, and traces of several accumulators, which
  also simplifies procedures by symbolic execution, with the trace equation
  systems of their loops as attached invariants (`-slice`), see
  [doc/prove.md](doc/prove.md).
- **Rewrite engine** for lemmas, part of `-prove`, and the
  **fallback** of the remaining goals to first-order logic (`-fallback`).
- **Solvers** z3 and cvc5 (`-z3`, `-cvc5`), and **answers** `correct`,
  `incorrect`, or `unknown` as in SV-COMP to every goal and lemma.

## Competition preview (SV-COMP 2027)

**[Cuvée: Loop Summaries by Trace Equation Systems and a Lemma Database
(Competition Preview)](doc/paper/cuvee.tex)** describes the approach, the
software architecture, the results on ReachSafety-Arrays and
ReachSafety-Loops against the official results of SV-COMP 2026, and the
setup of Cuvée in SV-COMP 2027. [doc/paper/README.md](doc/paper/README.md)
explains how to build it and where its numbers come from. The tool archive of
the competition version is
[10.5281/zenodo.23317707](https://doi.org/10.5281/zenodo.23317707). The
paper was generated with AI, see its AI Declaration.

## Dependencies

- Java 21 (a JDK to build, a JRE to run).
- [mill](https://mill-build.org) to build and test.
- z3 for `-z3` (the archive for SV-COMP bundles it next to `Cuvee.sh`, which
  puts that directory first on the `PATH`), cvc5 for `-cvc5`; both for the
  tests.
- Python 3 for the scripts of the experiments, LaTeX for the paper.

## Installation

```sh
git clone https://github.com/gernst/cuvee-plus.git
cd cuvee-plus
```

## Compilation

```sh
mill -i assembly                          # build out/assembly.dest/out.jar
cp out/assembly.dest/out.jar cuvee.jar    # the jar that Cuvee.sh runs
mill -i test                              # run the tests (CUVEE_PRINTING=1 after parser or printer changes, CUVEE_ALGORITHMS=1 for the slow suite)
```

`make` does the first two steps. `make native` builds `cuvee.native`, a native
executable that starts in milliseconds, with GraalVM's `native-image` (by
default GraalVM CE 25 from coursier, see the `Makefile`), which
`Cuvee-native.sh` runs like `Cuvee.sh` the jar; it has only been tried on a
few examples (in the VerifierCloud: `xml/cuvee-native.xml`, doc/benchmarks.md).

## Usage

```sh
./Cuvee.sh [options] file
```

Without options, the input is printed in its own language after parsing and
type checking. Transformations are applied in the order in which they are
given, the output options apply to the result. For example:

```sh
./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/max.dfy              # verify methods
./Cuvee.sh -chc -entry max -z3 examples/dafny/vcgen/max.dfy     # infer invariants
./Cuvee.sh -teq -prove examples/dafny/vcgen/sum.dfy             # Trace Equation Systems
./Cuvee.sh -chc -z3 examples/c/horn/count.c                     # C, invariants by Horn clauses
```

All options are documented in [doc/options.md](doc/options.md); `-help`
lists them.

## Features


- **Frontends:** SMT-LIB 2 (`.smt2`, extended by procedures and programs),
  a subset of Boogie (`.bpl`), a subset of Dafny (`.dfy`), SV-LIB 1.0
  (`.svlib`, without unstructured control flow, mutual recursion, the
  properties `:recurring` and `:not-recurring`, and witnesses), and simple
  integer programs in C (`.c`), with arrays as values and the verification
  conventions of SV-COMP, also given by SV-COMP task definitions (`.yml`)
  with a single input file in C or SV-LIB; the sizes of integer types follow 32 or 64 bit
  Linux (`-arch 32|64`, by default 64, or the data model of the task), and
  unsigned integers wrap around and the values of `__VERIFIER_nondet_<type>()`
  are within the range of their type (`-unbounded`: neither, the values of
  unsigned types are only nonnegative). All are parsed into the same core, are type
  checked with polymorphism, and resolve overloaded arithmetic on `Int` and
  `Real`, and indexing of arrays and sequences. In Dafny, lemmas are written
  as in Dafny, `lemma name<a>(xs) returns (ys) requires φ ensures ψ` for
  `forall xs :: φ ==> exists ys :: ψ`, assumed without a body (`free`) and
  to be proved with an empty one; functions may be recursive, defined by
  `match` with constructor patterns; the right-hand side `*` of an
  assignment or initializer gives an arbitrary value (there is no `havoc`);
  `a[i][j] := v` updates nested arrays; axioms, lemmas, and goals may be
  written `if φ then ψ` for `φ ==> ψ`, also below the quantifiers at the top,
  where `else` is optional.
- **Printers:** any input can be printed as SMT-LIB, Boogie, Dafny, or C
  (`-print smt2|bpl|dfy|c`), within the limits of each language, laid out
  for lines of 80 characters (`-linewidth <n>`), without the declarations
  of given features (`-known dfy,teq`, e.g. a C program without the logic of
  its Dafny source), and its logic in Lean 4
  (`-print lean`, e.g. the goals of `-vcgen`): sorts, datatypes, functions,
  axioms, lemmas, and goals, but no programs.
- **Implementations** (`-implement`): built-in sorts and functions, e.g.
  sets, get implementations that programs are verified against, functions
  and possibly nondeterministic methods with `{:implement pattern}`, from
  modules such as `-include implement:renc`; `-instrument` inlines the
  methods instead of calling them, e.g. for `renc`, maps
  and sets by the heap encoding Enc_R, whose contents a Horn solver infers
  (`-chc`, [examples/dafny/renc](examples/dafny/renc))
  ([doc/implement.md](doc/implement.md)).
- **Verification conditions** (`-vcgen`): weakest preconditions for
  procedures, covering:
  - contracts (`requires`, `ensures`, `modifies`) and `old(e)`;
  - loops with invariants, including `break`, `continue` and `return`;
  - termination measures (`decreases`);
  - global variables;
  - nondeterministic choice and iteration;
  - calls by the contract of the callee, inlined if it has a body and no
    contract.
- **Trace equation systems** (`-teq`): verification conditions by symbolic
  execution, where each loop is summarized by a trace equation system: one
  trace per strongly connected component of the read relation of the modified
  variables (one per variable where they do not read each other),
  `trace(e, for Y do x, y :: u)`, whose update
  `u` is an expression or guarded cases `case φ => e`, and the constraint that
  all earlier iterations took a path through the body,
  `invs(for Y check y :: φ)` (in Boogie `all(...)`, in SMT-LIB `invs`), where
  the dependencies are traces without their last element, `⌊X⌋` in Dafny and
  Boogie (`butlast`, sort `Trace<T>`); `maps(for Y yield y :: e)` maps traces
  element by element. Functions of the database that are traces are defined
  with `{:fold}`, whose definition is a rule that folds such a trace into
  the function.
  Loop-free programs go directly to a solver,
  loops need rewriting by lemmas first: `-teq` injects the lemma database
  [teq.dfy](resources/cuvee/teq.dfy) once at the beginning of its output,
  whose rewrite rules `-prove` applies, e.g. the counter lemma;
  `-include teq:<concept>` adds a module of
  [resources/cuvee/teq](resources/cuvee/teq) (`aggregation`, `arithmetic`,
  `arrays`, `counters`, `search`, `sorted`, `strides`, `unsigned`, `series`; the former
  `nested` is in `resources/cuvee/legacy`). The lemmas of the migrated modules (teq.dfy, `aggregation`,
  `arithmetic`, `search`, `sorted`, `arrays`, `counters`, `strides`, `unsigned`, `series`) are proved in Lean 4 ([lean/](lean)), against
  statements generated from the modules, checked by `scripts/lean/check.sh`. The former single file
  [legacy/teq.dfy](resources/cuvee/legacy/teq.dfy) is kept but no longer injected. `-rules` reports the rules that
  `-prove` applies to each goal, as `(set-info :used ...)`. `-fallback` encodes the trace equation systems that remain
  into first-order logic for the solvers.
- **Constrained Horn clauses** (`-chc`): the same programs as Horn clauses
  for invariant inference. `-flat` then replaces record arguments of the
  predicates by their fields.
- **Entry point** (`-entry <name>`): the procedure where executions start,
  `main` in C by default (as in SV-COMP); `-chc` needs one outside C (SV-LIB
  starts at its `verify-call` commands), `-teq` emits a goal only for it, the
  other procedures are checked inlined at their calls, `-vcgen` ignores it and
  checks every procedure against its contract.
- **Monomorphization** (`-monomorph`): polymorphic functions are replaced by
  their instances, which the solvers require.
- **Splitting** (`-split`): goals and lemmas are split into individual
  obligations `forall xs. antecedents ==> conclusion`, which the solvers report
  one by one.
- **Deduction engine** (`-prove`): contextual simplification of formulas and
  function definitions, and of procedures by symbolic execution, which keeps
  their structure and forgets nothing (with `-slice`, the head of each loop is
  its trace equation system, attached as an invariant over the program
  variables, e.g. `tot == 2 * idx && idx <= len && 0 <= idx`), with congruence closure and a simplex
  over the rationals as the context, matching modulo the classes, the
  per-variable views of traces of several accumulators (one trace per strongly connected
  component of the variables of a loop, `-teq`), rules over whole
  cycles, and forward lemmas (`{:fw}`); normalisation of arithmetic on `Int`
  and `Real` into polynomials, comparisons with positive coefficients, and
  derivatives; see [doc/prove.md](doc/prove.md).
- **Rewrite engine**: conditional rules `lhs = rhs if cond` from the
  assertions and lemmas with the attribute `:rw` (`axiom {:rw} φ`,
  `lemma {:rw} name(xs) requires ψ ensures φ` in Dafny, `lemma {:rw} φ;` in
  Boogie, `(assert (! φ :rw))` in SMT-LIB), where
  `φ` is a universally quantified equation, equivalence, negation, or boolean
  atom, optionally with a premise as condition, and from function definitions
  with `:rw` whose body is a match on a parameter (one rule per case),
  applied by `-prove` after each round,
  matching modulo associativity, commutativity, and 0 of `+` and `-`, and the
  binding structure of the trace combinators `trace`, `maps`, and `invs` from
  *Trace Equation Systems for Program Verification*.
- **Solvers** (`-z3`, `-cvc5`, `-timeout <ms>`), which check the output:
  goals and lemmas are checked for validity and answered `correct`,
  `incorrect`, or `unknown`, and assertions and `check-sat` are passed
  through. Lemmas with the attribute `free` (Dafny lemmas without a body) are
  assumed without proof, like axioms, although they are meant to follow from
  the theory.
- **Answers**: every goal and lemma that is not free is answered `correct`,
  `incorrect`, or `unknown` when it is given, by the solver, or without
  solver by its form (`true`, `false`); the answers to the outputs of a goal
  are combined, e.g. the parts of `-split`, a goal dropped since it was
  reduced to `true` is `correct`, and a procedure has one answer per goal
  that `-vcgen` or `-teq` generates. A refutation is
  `unknown` if the goal is `:abstract`, i.e., stronger than the
  specification: a loop without invariant under `-vcgen`, the lowering of
  `-fallback`, or a function declared `:abstract` that the goal applies, e.g.
  the bit operations of C, uninterpreted on integers other than 0 and 1.
  `-chc` answers its `check-sat` `correct` for `sat` and `incorrect` for
  `unsat`, followed by the model. `-quiet` prints the answers only, not the
  output.

Known limitations and planned work are listed in [TODO.md](TODO.md), bugs in [bugs.md](bugs.md).

## SV-COMP

Cuvée takes part in SV-COMP 2027 in the categories ReachSafety-Arrays and
ReachSafety-Loops (C, property `unreach-call`) and in SV-LIB.Overall with
SV-LIB.correct-tags.CoreVerification and SV-LIB.correct-tags.CTranslated
(SV-LIB scripts, property `correct-tags`), with the same command for both:

```sh
./Cuvee.sh -svcomp -fallback -z3 -timeout 900000 [-arch 32|64] task
```

where `-svcomp`, as the first argument, stands for `-teq` with all modules of the lemma database,
`-prove -split -prove -split -prove`, and `-witness witness.yml` (see doc/options.md). The answers are `correct`,
`incorrect`, or `unknown`, one per goal: the
property is violated if one is `incorrect`, and holds if all are `correct`.
Executions of a C program start in `main`, the entry point (`-entry <name>`
selects another one): `-teq` emits a goal for `main` only and checks the
other functions inlined at their calls, in their context; in SV-LIB, the
`verify-call` commands are the entry points;
With `-witness <file>`, Cuvée writes a witness of SV-COMP for the answer to a C program: without invariants for
true, with the call of `reach_error` as the target for false, which leave the proof or the search for the path to
the validator (see doc/options.md).
`-chc -z3` (Horn clauses) and `-vcgen -z3` (the annotations as
given, `unknown` for loops without invariant) are alternatives that are not
used in the competition. The SV-LIB frontend does not support labels and
gotos, `define-procs-rec`, the properties `:recurring` and `:not-recurring`, and
witnesses, and it rejects tags on statements other than loops and procedure
bodies (see [doc/architecture.md](doc/architecture.md) and [TODO.md](TODO.md)).

Results (15 min, `-verify`, all modules of the lemma database, on the valid
tasks of SV-COMP 2026; see [doc/paper](doc/paper)): on ReachSafety-Arrays,
131 tasks proved without and 141 with z3, 112 of which none of Symbiotic,
UAutomizer, CPAchecker, and Korn reports as true in the official results;
on ReachSafety-Loops, 126 without and 280 with z3. Without `-fallback`, no
result is wrong. Known problems of `-fallback`: 7 wrong proofs
(`fermat1-ll_unwindbound*`, where the exits of nested loops had overlapping
guards, whose lowering contradicted itself, fixed in 0.42.2, see
[doc/teq.md](doc/teq.md)) and 2 wrong refutations (`sanfoundry_24-1`,
`verifythis/lcp`), where functions that `main` calls only in a certain context
were also checked for arbitrary arguments, which the entry point fixes (see
below and [doc/architecture.md](doc/architecture.md)). The runs included the modules `nested`, `sorting`, and
`strides`, which the competition command does not load.

- [cuvee.py](cuvee.py): the tool-info module of BenchExec, which interprets
  the answers (any `incorrect` is false, all `correct` true, for every
  property); submitted to BenchExec as `benchexec/tools/cuvee.py`
  ([sosy-lab/benchexec#1327](https://github.com/sosy-lab/benchexec/pull/1327)).
  The entry of fm-tools (`data/cuvee.yml`, merge request !1176 of
  [fm-tools](https://gitlab.com/sosy-lab/benchmarking/fm-tools)) gives the
  options, the categories, and the DOI of the archive.
- `./benchmark xml/<definition>.xml -r <rundefinition> -t <tasks>` runs Cuvée
  and other verifiers on the tasks of both categories with BenchExec, whose results
  [scripts](scripts) summarize (`table.py`, `scatter.py`, `quantile.py`,
  `rules.py`, `compare.py`; see [doc/benchmarks.md](doc/benchmarks.md)). [SV-COMP.md](SV-COMP.md) records the results and the
  limitations found.
- [archive](archive): the README, `smoketest.sh`, and examples of the archive
  for the competition; `scripts/zenodo.py package` builds `dist/cuvee.zip`
  from the last commit and runs its smoke test (`-svcomp`, `-svcomp -fallback
  -z3`, and `-chc -z3` on a safe and an unsafe C program and SV-LIB script),
  `upload` puts it into a draft on Zenodo (with a personal access token, see
  the script), which is published by hand. The archive of the current version
  in fm-tools is 0.52.17,
  [10.5281/zenodo.23713558](https://doi.org/10.5281/zenodo.23713558); the
  paper cites the earlier
  [10.5281/zenodo.23317707](https://doi.org/10.5281/zenodo.23317707).
- [doc/paper](doc/paper): the competition preview (LNCS), see
  [above](#competition-preview-sv-comp-2027).

## Documentation

- [doc/options.md](doc/options.md): the command line options.
- [doc/architecture.md](doc/architecture.md): the pipeline, the packages, and
  how a run flows through them.
- [doc/datastructures.md](doc/datastructures.md): the core representation of
  types, expressions, programs, commands, and the state.
- [doc/teq.md](doc/teq.md): trace equation systems, the combinators, and the
  lemma database.
- [doc/hybrid.md](doc/hybrid.md): derivatives, differential equations, and
  parallel composition.
- [doc/style.md](doc/style.md): coding style.
- [ideas](ideas): proposals and experiments that are not implemented.

## License

Cuvée is licensed under the Apache License 2.0 ([LICENSE](LICENSE)). The
archive for SV-COMP includes software under its own licenses: Z3
([LICENSE.z3](LICENSE.z3)), the Scala library
([LICENSE.scala](LICENSE.scala)), sourcecode
([LICENSE.sourcecode](LICENSE.sourcecode)), and SnakeYAML Engine
([LICENSE.snakeyaml](LICENSE.snakeyaml)).

## Acknowledgement

This code was developed with the help of Claude Code, using the models Claude
Opus and Claude Fable by Anthropic.
