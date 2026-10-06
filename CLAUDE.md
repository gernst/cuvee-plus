# Cuvée

A verification toolchain in Scala 3: frontends for SMT-LIB, Dafny, Boogie, and
C produce one core representation, which transformations (verification
conditions, trace equation systems, Horn clauses, simplification) and printers
or solvers consume.

## Read first

- [doc/architecture.md](doc/architecture.md): pipeline, packages, stages,
  frontends, tests.
- [doc/datastructures.md](doc/datastructures.md): the core and the simplifier.
- [doc/teq.md](doc/teq.md): trace equation systems (`-teq`), combinators,
  lemma database.
- [doc/hybrid.md](doc/hybrid.md): derivatives, ODEs, parallel composition
  (`-hybrid`).
- [doc/style.md](doc/style.md): coding style, incl. lowercase comments that
  explain why.
- [TODO.md](TODO.md): open problems and the user's instructions.

## Workflow

- New algorithms need not close every goal: report which remain and why.
- Commit each finished item once it compiles and all tests pass, without
  being asked: one line `area: what changed; ...; version X.Y.Z`.
- Bump `Config.version` ([src/cuvee/Config.scala](src/cuvee/Config.scala))
  in every commit: second digit for major features, third for minor ones.
- After each commit: `mill -i assembly; cp out/assembly.dest/out.jar cuvee.jar`.
- Never commit the user's untracked scratch files (e.g. `*.dfy` at the root).
- Every feature gets tests (unit tests and/or `examples/<language>/`). Update
  changed expected outputs deliberately and say so.

## Commands

- Test: `mill -i test` (four groups; check every `Tests: n, Passed: n,
  Failed: 0` line, failures are marked `X`).
- Run: `mill -i run <options> <file>`. `-print` takes an argument
  (`-print null`).
- z3 by hand only with a timeout: `z3 -T:5 file.smt2`.
- The shell is fish; write multi-line scripts for bash explicitly.

## Trace equation systems and solvers

- `Trace` exists only with `-teq` (defined in
  [teq.dfy](resources/cuvee/teq.dfy)); never include it implicitly or in
  preludes.
- The don't have to prove `-teq` goals on their own: no trace special cases
  in the solver interface, no implicit monomorphization, no implicit TEQ
  concepts passed to the solver.

## Caveats

- **Combinator dependencies** have type `Seq(T)`, at least one, of equal
  length (`Seqs.len`).
- **The simplifier runs only in `-simplify`.** Other transforms never call it
  or its helpers.
- **Simplifier helpers are local.** Each normalizes its own constructor, in
  one step, building with the normalizing helpers (`not(...)`, not
  `Not(...)`). The outer loops iterate. No global normal forms, no further
  case splits.
- **Helpers used as decisions** (e.g. `eq_(...) == True`) get
  `ctx.neutral`.
- **Expected values in unit tests** must be in the simplifier's normal form.
- **Polymorphic assertions** need `lemma <a> ...`. Never run z3 or
  `-monomorph` on polymorphic input; such tests only generate goals
  (`-print null`).
- **Testing teq.dfy lemmas:** on core terms with `Rules.from(TEQ.lemmas)` and
  `Rewrite`.
- **Preludes** are injected into the stream; transforms see them, tests that
  call a `Source` directly drop `Examples.prelude(...)`.
- **Stages buffer declarations**, losing the sink's answers to them; filters
  that need those are sink wrappers.
- **Pretty printing:** wrap parenthesized documents in `Align(...)`.
- **Imports:** import `cuvee.Error` and `cuvee.Debug` instead of using
  qualified names.
- **Dafny output need not be valid Dafny,** e.g. tuple selectors print as
  `tuple2_1(p)`, not `p.1`; do not fix such cases unless asked.
- **Test catches the bug?** Stash only the fix, run
  `mill -i test.testOnly <suite>`.
- **Mill launcher crashes** (`MillLauncherMain`) are transient; rerun.
- **Unrelated changes in the tree:** stash them before the version-bump
  commit.
- **Rejected tool calls may have taken effect:** check `git status` and
  revert.
