# Cuvée

A verification toolchain in Scala 3: frontends for SMT-LIB, SV-LIB, Dafny,
Boogie, and C produce one core representation, which transformations (verification
conditions, trace equation systems, Horn clauses, simplification) and printers
or solvers consume.

## Read first

- [doc/architecture.md](doc/architecture.md): pipeline, packages, stages,
  frontends, tests.
- [doc/datastructures.md](doc/datastructures.md): the core.
- [doc/teq.md](doc/teq.md): trace equation systems (`-teq`, one trace per
  strongly connected component of a loop's variables), combinators, lemma
  database.
- [doc/prove.md](doc/prove.md): the deduction engine (`-prove`, package
  `prove`), simplification, rewriting, and facts that the goal does not
  mention.
- [doc/hybrid.md](doc/hybrid.md): derivatives, ODEs, parallel composition
  (`-hybrid`).
- [doc/implement.md](doc/implement.md): implementations of sorts and functions
  (`-implement`, `-include implement:<name>`).
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
  item is finished (compiles, all tests pass), report and wait. Messages
  follow the usual convention: a short summary line `area: what changed`
  (at most about 72 characters, no period), a blank line, then the details
  in a body wrapped at 72 characters (one paragraph or `-` item per
  change), ending with `version X.Y.Z` when the version changes.
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
  parser or a printer requires.
- Lean proofs of the stable database modules: `scripts/lean/check.sh`
  (`--regenerate` after changing a module of `MODULES` in
  scripts/lean/generate.py; see lean/README.md); `lean` works in the repository through
  `lean-toolchain`, `lake` only as `$(elan which lake)`.
- Run: `mill -i run <options> <file>`. `-print` takes an argument
  (`-print smt2`), `-quiet` prints no output.
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
  for `-prove`.
- `Trace` exists only with `-teq` (declared in
  [teq.dfy](resources/cuvee/teq.dfy)); never include it implicitly or in
  preludes.
- The lemma database: `-teq` injects [teq.dfy](resources/cuvee/teq.dfy), the
  entry point (`TEQ.modules`); `-include teq:<concept>` injects an optional
  module of [resources/cuvee/teq](resources/cuvee/teq) after it
  ([doc/teq.md](doc/teq.md)); the benchmark definitions include all of them.
  Before dropping a rule, check SV-COMP (`scripts/missing.py`,
  doc/benchmarks.md) and the examples, and keep a rule that only one task
  needs local to that task. Rules are tried in the order of the file, so it
  decides which abstraction a fragment gets.
- Counts, lengths and positions of the database are `int`; the definitions
  clamp (`counter(i, c, n)` is `stop(i)` for `n <= 0`), and a lemma states
  `requires 0 <= n` where it needs it. There are no naturals.
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
- A closed `invs` side condition is looked up among the facts modulo
  classes and renaming (`Rewrite.known`). A side condition may mention the term of the rule's own left-hand side
  (`l == current(Lv)` for a rule on `current(Lv)`): the rule is suspended while
  its conditions are evaluated (`Context.active`), so the instance is not
  rewritten by the rule itself.
- A fact that is needed where only its term occurs (a bound of
  `current(incs(...))`) is a forward lemma, `{:fw}`, not a rewrite rule on
  the atom: `-prove` assumes its instances wherever a term matching its
  trigger occurs in an assumed fact (`Forward`). Its trigger is tried at every
  matching term, also without an instance: trigger at a fold of the term, one
  fact per lemma (`-split` makes conjuncts lemmas of their own), no variables
  bound by conditions alone (doc/teq.md, "What a forward lemma costs").
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
  several accumulators yet (`doc/teq.md`).
- **The simplifier runs only in `-prove`.** Other transforms never call it
  or its helpers (`Split` uses `prove.Normalize.lift` only).
- **Calls carry the global variables that they modify** (`Call.vars`, the
  callee's modifies clause in its order), which `Type.check` fills in; build
  calls with `Nil` before the check. `Prog.mod` includes them, so it is
  complete: no lookups of `procattrs(name).modifies` at the consumers. Local
  variables and parameters must not shadow global variables; a loop without
  modifies clause may modify what its enclosing scope may. Questions about the
  statements of a program are methods of each kind (`returns`,
  `abstracts`, `calls`), there is no `subprogs`.
- **`-prove` simplifies procedures** (`Slice`, doc/prove.md "Programs"): the
  context speaks about choices only and forgets nothing, program variables are
  bound to terms over them, expressions are written back over the variables in
  scope; with `-slice`, the head of a loop is its trace equation system
  (`TEQ.head`), attached as an invariant.
- **Simplifier helpers are local.** Each normalizes its own constructor, in
  one step, building with the normalizing helpers (`not(...)`, not
  `Not(...)`). The outer loops iterate. No global normal forms other than the
  canonical forms of the context (`Classes.normalize`), no further case splits.
- **Canonical forms** (doc/prove.md, "The context"): one order of roots
  (`Context.order`, variables of outer scopes first); only solutions that
  are arithmetic over variables are substituted, never equations of traces
  or other terms, which the matcher reaches through their classes.
- **Helpers used as decisions** (e.g. `eq_(...) == True`) get
  `ctx.neutral`.
- **Expected values in unit tests** must be in the simplifier's normal form.
- **Polymorphic assertions** need `lemma name<a>(...)`. Never run z3 or
  `-monomorph` on polymorphic input; such tests only generate goals
  (`-quiet`).
- **Testing database lemmas:** on core terms with
  `Rules.from(State.empty, TEQ.lemmas)` (teq.dfy) and `prove.Rewrite`, with
  the modules they need parsed after it (`test/dafny/TEQ.scala`).
- **Preludes** are injected into the stream; transforms see them, tests that
  call a `Source` directly drop `Examples.prelude(...)`.
- **Stages buffer declarations**, except goals and lemmas that are not free,
  which flush and are answered immediately, by the combination of the answers
  to their outputs (doc/architecture.md, "Answers"); filters that need the
  answers to other declarations are sink wrappers.
- **Implementations** ([doc/implement.md](doc/implement.md)): patterns are a
  function applied to a permutation of all inputs, nothing more general;
  methods implement functions (possibly nondeterministically), methods are
  never implemented; the bodies of implementations are not rewritten.
- **Entry points:** `-teq` emits a goal for the entry point only and `-chc`
  starts from it (`Config.entry`: `-entry <name>`, otherwise `main` in
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
  the goals that a `verify-call` flushes are answered `correct`,
  `incorrect`, or `unknown` by the sink, which `cuvee.py` reads as a set
  (doc/architecture.md, "Answers"). Out of scope by decision: labels and gotos,
  `define-procs-rec`, `:recurring`, `:not-recurring`, `:decreases-lex`,
  witnesses and traces.
