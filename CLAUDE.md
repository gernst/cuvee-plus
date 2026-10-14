# Cuvée

A verification toolchain in Scala 3: frontends for SMT-LIB, SV-LIB, Dafny,
Boogie, and C produce one core representation, which transformations (verification
conditions, trace equation systems, Horn clauses, simplification) and printers
or solvers consume.

## Read first

- [doc/architecture.md](doc/architecture.md): pipeline, packages, stages,
  frontends, tests.
- [doc/datastructures.md](doc/datastructures.md): the core.
- [doc/simplifier.md](doc/simplifier.md): the simplifier, rewriting, fusion, and
  facts that the goal does not mention.
- [doc/teq.md](doc/teq.md): trace equation systems (`-teq`, one trace per
  strongly connected component of a loop's variables), combinators, lemma
  database.
- [doc/prove.md](doc/prove.md): the deduction engine (`-prove`, package
  `prove`, independent of `simplify`), its record in
  [doc/prove.md](doc/prove.md).
- [doc/hybrid.md](doc/hybrid.md): derivatives, ODEs, parallel composition
  (`-hybrid`).
- [doc/style.md](doc/style.md): coding style, incl. lowercase comments that
  explain why.
- [doc/options.md](doc/options.md): the command line options.
- [doc/benchmarks.md](doc/benchmarks.md): runs in the VerifierCloud, definitions, results, comparison scripts.
- [TODO.md](TODO.md): open problems and the user's instructions.
- [bugs.md](bugs.md): wrong results (soundness first), errors, crashes, non-termination.
- [ideas/](ideas): proposals and experiments, not implemented (index in ideas/README.md).

## Workflow

- New algorithms need not close every goal: report which remain and why.
- Commit only when the user explicitly says so, never on your own; when an
  item is finished (compiles, all tests pass), report and wait. Messages are
  one line `area: what changed; ...; version X.Y.Z`.
- Bump `Config.version` ([src/cuvee/Config.scala](src/cuvee/Config.scala))
  in every commit that changes Scala code: second digit for major features,
  third for minor ones. Commits without Scala changes (examples, docs,
  benchmark definitions) keep the version and omit it from the message.
- After each commit: `mill -i assembly; cp out/assembly.dest/out.jar cuvee.jar`.
- Never commit the user's untracked scratch files (e.g. `*.dfy` at the root).
- Every feature gets tests, preferably example files whose first line is
  their command line (`// ./Cuvee.sh <options> <file>`, `; ./Cuvee.sh ...` in
  SMT-LIB and SV-LIB) with the expected
  `name.out`/`name.err`; unit tests only where the command line cannot observe
  it. Tests never write files. Regenerate changed expected outputs by hand
  (`./Cuvee.sh <options> <file> > name.out 2> name.err`, after the assembly)
  deliberately and say so; `./Cuvee.sh -test <file>` checks one.

## Commands

- Test: `mill -i test` (four groups; check every `Tests: n, Passed: n,
  Failed: 0` line, failures are marked `X`). The algorithms of
  `examples/dafny/algorithms` run only with `CUVEE_ALGORITHMS=1 mill -i test`
  (about five minutes), the roundtrip suites of the printers (every example
  printed and parsed back) only with `CUVEE_PRINTING=1`, which a change of a
  parser or a printer requires, the SV-COMP databases only with
  `CUVEE_SVCOMP=1`.
- Lean proofs of the stable database modules: `scripts/lean/check.sh`
  (`--regenerate` after changing a module of `MODULES` in
  scripts/lean/generate.py; see lean/README.md); `lean` works in the repository through
  `lean-toolchain`, `lake` only as `$(elan which lake)`.
- Run: `mill -i run <options> <file>`. `-print` takes an argument
  (`-print null`).
- z3 by hand only with a timeout: `z3 -T:5 file.smt2`.
- Commands that may read stdin hang otherwise: `java -jar cuvee.jar` only
  with a file, a timeout, and `< /dev/null`; mill in scripts with
  `< /dev/null`.
- The shell is fish; write multi-line scripts for bash explicitly.
- Benchmarks: `./benchmark xml/<definition>.xml -r <rundefinition> -t <tasks>`,
  never with several `-t <tasks>` in one call: tasks of different sets with
  the same name (e.g. the C and Dafny versions in `benchmarks/sv-comp`) get
  each other's results. Start one call per set instead, in parallel if
  needed.

## Trace equation systems and solvers

- `-teq` partitions the variables of a loop by
  the strongly connected components of their read relation, one trace per
  component, of several accumulators for a cycle (`TEQ.system`); its goals are
  for `-prove`, since `-simplify` does not know traces of several
  accumulators. The per-variable form of the paper is gone (Oct 13, 2026).
- `Trace` exists only with `-teq` (declared in
  [teq.dfy](resources/cuvee/teq.dfy)); never include it implicitly or in
  preludes.
- The lemma database: `-teq` injects [teq.dfy](resources/cuvee/teq.dfy), the
  entry point (`TEQ.modules`); `-include teq:<concept>` injects an optional
  module of [resources/cuvee/teq](resources/cuvee/teq) after it. The optional
  modules were written for the per-variable form and are migrated into modules
  over teq.dfy alone ([doc/teq.md](doc/teq.md)), `nested` retired to `legacy/`;
  the benchmark definitions include all migrated ones. Rules left out of a
  module stay in [legacy/](resources/cuvee/legacy); before dropping a rule,
  check SV-COMP (`scripts/missing.py`, doc/benchmarks.md).
  [legacy/teq.dfy](resources/cuvee/legacy/teq.dfy) is the former single file
  of the per-variable form: a backup, not injected. Rules are tried in the
  order of the file, so it decides which abstraction a fragment gets.
- Tests of trace equation systems are Dafny examples only, not SMT-LIB or
  Boogie. Those that should not pull in the lemma database of `-teq` duplicate
  the declarations of `teq.dfy` that they need, with its indexed names (e.g.
  `type Trace<a₀>`, `function counter(x₀: int, x₁: int, x₂: int): Trace<int>`),
  and bind the variables of their context with `forall`, not as constants.
- Variables of methods and of example-local lemmas must be named apart from
  the variables of the database rules (`Ks`, `Ns`, `Js`, `x`, `n`, ...): a
  clash captures the name, conditions are decided vacuously or the goal is
  replaced by a "variables of a rule not instantiated" error.
- Example-local summary lemmas match the fragment forms that the included
  modules produce; a file includes only the modules its lemmas are written
  for. Examples that do not terminate stay in the tree and are listed in
  `Examples.nonterminating`.
- A closed `invs` side condition is decided, not matched, and fails under
  `-simplify`: write it over a fresh list variable and identify it by an
  equation (`Js2 == Js`); `-prove` looks closed conditions up among the facts
  modulo classes and renaming (`Rewrite.known`), which needs no such variable.
  A side condition may mention the term of the rule's own left-hand side
  (`l == current(Lv)` for a rule on `current(Lv)`): the rule is suspended while
  its conditions are evaluated (`Context.active`), so the instance is not
  rewritten by the rule itself.
- A fact that is needed where only its term occurs (a bound of
  `current(incs(...))`) is a forward lemma, `{:fw}`, not a rewrite rule on
  the atom: `-prove` assumes its instances wherever a term matching its
  trigger occurs in an assumed fact (`Forward`); `-simplify` does not use them.
- Long runs use a private copy of `cuvee.jar`: a rebuild during a run crashes
  the JVM, and the checkout's jar may contain uncommitted changes.
- Runs on `-teq` examples take a timeout and one core
  (`timeout 300 nice -n 19 taskset -c 0 java -cp cuvee.jar cuvee.Cuvee ...`),
  and check the exit status: a killed run prints no goals and looks like a
  full proof.
- The don't have to prove `-teq` goals on their own: no trace special cases
  in the solver interface, no implicit monomorphization, no implicit TEQ
  concepts passed to the solver.

## Caveats

- **Combinator dependencies** have type `List(T)`, at least one, of equal
  length (`List.len`).
- **Traces have one or several accumulators** (`Trace(inits, deps, accs,
  bound, results)`): match the single case with `Trace.single`, build it with
  `Trace(init, deps, acc, bound, update)`; the components of a trace of
  several are read by `Component(S, i)` and `History(S, i)` only, never by
  tuple selectors. Only the Dafny frontend and printer know the syntax of
  several accumulators yet (`doc/teq.md`), and only `-prove` simplifies such
  traces.
- **The simplifier runs only in `-simplify`.** Other transforms never call it
  or its helpers. The engine of `-prove` (package `prove`) copies what it
  needs from `simplify` and never references it; changes to one are not
  mirrored in the other unless asked.
- **Simplifier helpers are local.** Each normalizes its own constructor, in
  one step, building with the normalizing helpers (`not(...)`, not
  `Not(...)`). The outer loops iterate. No global normal forms, no further
  case splits.
- **Helpers used as decisions** (e.g. `eq_(...) == True`) get
  `ctx.neutral`.
- **Expected values in unit tests** must be in the simplifier's normal form.
- **Polymorphic assertions** need `lemma name<a>(...)`. Never run z3 or
  `-monomorph` on polymorphic input; such tests only generate goals
  (`-print null`).
- **Testing database lemmas:** on core terms with
  `Rules.from(State.empty, TEQ.lemmas)` (teq.dfy) and `Rewrite`; the tests of
  the rewriting of `-simplify` on lemmas of the former database parse
  `legacy/teq.dfy` (`test/dafny/TEQ.scala`).
- **Preludes** are injected into the stream; transforms see them, tests that
  call a `Source` directly drop `Examples.prelude(...)`.
- **Stages buffer declarations**, losing the sink's answers to them; filters
  that need those are sink wrappers.
- **Entry points:** `-teq` emits a goal for the entry point only and `-chc`
  starts from it (`Config.entryPoint`: `-entry <name>`, otherwise `main` in
  C; SV-LIB starts at its `verify-call` commands); the other procedures are
  checked in the context of their calls. `-vcgen` checks every procedure
  against its contract.
- **Pretty printing:** wrap parenthesized documents in `Align(...)`.
- **Imports:** import `cuvee.Error` and `cuvee.Debug` instead of using
  qualified names.
- **No local shorthand helpers** like `def e(expr: Expr) = expand(state, expr)`;
  write the call inline, e.g. `args.map(expand(state, _))`.
- **Dafny output need not be valid Dafny,** e.g. tuple selectors print as
  `tuple2_1(p)`, not `p.1`; do not fix such cases unless asked.
- **Test catches the bug?** Stash only the fix, run
  `mill -i test.testOnly <suite>`.
- **Mill launcher crashes** (`MillLauncherMain`) are transient; rerun.
- **Unrelated changes in the tree:** stash them before the version-bump
  commit.
- **Rejected tool calls may have taken effect:** check `git status` and
  revert.
- **SV-LIB:** `annotate-tag` and `verify-call` are the core commands
  `AnnotateTag` and `VerifyCall`; the parser resolves the terms of an
  annotation in the scope of the tagged statement, the transforms attach the
  annotations to loops and procedures when the `verify-call` flushes them
  (`State.annotated`); tags are allowed on loops and procedure bodies only;
  with `-verify`, each `verify-call` is answered `correct`, `incorrect`, or
  `unknown` (`pipe.Verify`), which `cuvee.py` reads. Out of scope by decision: labels and gotos,
  `define-procs-rec`, `:recurring`, `:not-recurring`, `:decreases-lex`,
  witnesses and traces.
