# Cuvée

A verification toolchain in Scala 3: frontends for SMT-LIB, Dafny, Boogie, and
C produce one core representation, which transformations (verification
conditions, trace equation systems, Horn clauses, simplification) and printers
or solvers consume.

## Read first

- [doc/architecture.md](doc/architecture.md): the pipeline, the packages, the
  stages, the frontends, the tests.
- [doc/datastructures.md](doc/datastructures.md): the core (types, functions,
  expressions, programs, commands, state, substitutions, simplifier).
- [doc/teq.md](doc/teq.md): trace equation systems (`-teq`), the
  combinators, the lemma database, their simplification and rewriting.
- [doc/hybrid.md](doc/hybrid.md): derivatives, differential equations, and
  parallel composition (`-hybrid`).
- [doc/style.md](doc/style.md): coding style. Match it, including comments
  in lowercase prose that explain why.
- [TODO.md](TODO.md): open problems and the user's instructions, grouped by
  area.

## Workflow

- When developing new algorithms (e.g. in the simplifier or the rewriting),
  not every proof goal must close. The aim is reasonable progress: report
  which goals remain and why, instead of forcing them through.
- Commit after each finished item, once it compiles and all tests pass,
  without being asked. Messages are one line, `area: what changed; ...`,
  ending in `; version X.Y.Z`.
- After each commit, regenerate `cuvee.jar` (gitignored):
  `mill -i assembly; cp out/assembly.dest/out.jar cuvee.jar`.
- Bump `Config.version` in [src/cuvee/Config.scala](src/cuvee/Config.scala)
  in every commit: the second digit for major features (resetting the third),
  the third for minor ones.
- Questions for the user go into TODO.md as a note on the item, rather than
  blocking; continue with the other pending instructions meanwhile.
- Keep the instruction lines at the top of TODO.md
  ("New TODOs ... (provided by user)") when rewriting the file. Remove items
  once done and add new limitations there, not in code comments.
- Do not commit the user's untracked scratch files (e.g. `*.dfy` at the root).
- Every feature gets tests (unit tests on core terms and/or an example in
  `examples/<language>/`). Changing the simplifier or the lemma database can
  change expected outputs (`examples/simplify/*.expected.smt2`, the TEQ tests).
  Update them deliberately and say so.

## Commands

- Build and test: `mill -i test` (there is no `./mill` wrapper). The tests run
  in four forked groups. Check that every `Tests: n, Passed: n, Failed: 0`
  line is clean, and find failures by the marker `X` in the output.
- Run: `mill -i run <options> <file>`, e.g.
  `mill -i run -teq -simplify examples/dafny/vcgen/sum.dfy`. Without `-print`,
  the output is printed in the language of the input. `-print` takes an
  argument (e.g. `-print null` in tests), so `-print file.dfy` is an error.
- z3 by hand always with a timeout: `z3 -T:5 file.smt2`.
- The shell is fish. Write multi-line scripts for bash explicitly.

## Trace equation systems and solvers

Details in [doc/teq.md](doc/teq.md).

- `Trace` (and `butlast`) must never be included implicitly. They exist only
  with `-teq`, whose lemma database [teq.dfy](resources/cuvee/teq.dfy)
  defines them. Inputs that use traces without `-teq` declare `Trace`
  themselves. Do not put it into the preludes.
- SMT solvers are not expected to solve TEQs. The simplifier must prove the
  goals of `-teq` on its own. Hence:
  - no special cases for traces in the solver interface;
  - no implicit monomorphization;
  - no implicit introduction of TEQ concepts (sorts, functions, lemmas) to
    the solver.

## Things that were easy to get wrong

- **Combinator dependencies are sequences.** The dependencies of `Trace`,
  `Maps`, and `Invs` always have type `Seq(T)`, at least one, of equal length.
  Their length is `Seqs.len` (theory of sequences), not `Fun.trace.length`.
  A trace of `n` steps has `n + 1` elements, `⌊X⌋` has `n`.
- **The simplifier runs only as the transform of `-simplify`.** Other
  transforms (e.g. `Verify`, `TEQ`) never call it, not even its pure
  helpers such as `Simplify.diff`; they produce their goals as they are and
  leave simplification to `-simplify`.
- **Simplifier helpers are local.** Each helper (`and`, `or`, `not`, `ite`,
  `imp`, `eq_`, `invs`, ...) normalizes its own constructor only:
  - Build further formulas with the normalizing helpers (`not(...)`, not
    `Not(...)`), except in the fallthrough case of the helper itself.
  - Do not re-check what the outer loop decides, e.g. complementary
    conjuncts, which `nary` finds by simplifying each argument under the
    others.
  - Prefer local transformations over global normal forms. E.g. common
    disjuncts are factored out of conjunctions, but there is no CNF/DNF.
- **Lemmas and attributes.** `{:rw}` makes a lemma a rewrite rule of
  `-simplify`. `{:free}` makes the solver assume it without proof. A lemma
  without `{:free}` is proved by the solver, which fails for uninterpreted
  functions. Rules have the shape `∀ xs. if φ then l == r` (or `<==>`,
  `!p`, `p`). The variables of `r` and `φ` must occur in `l`. A rule must not
  loop: keep looping lemmas `{:free}` only.
- **Type parameters of assertions.** `lemma <a> {:rw} φ` (Dafny and Boogie).
  Without the declaration, `forall v: a` is "unknown type". `-monomorph`
  does not instantiate polymorphic assertions. So polymorphic axioms must not
  go into examples that the solver tests verify (e.g. `syntax.bpl`). Use
  `traces.bpl` and `sorts.dfy` instead.
- **Dafny syntax facts.**
  - Parenthesized expressions are `Tuple(List(e))` in the syntax. That is
    how chained comparisons (`0 <= i < n`, built by `Grammar.chain`) are
    told apart from `(x == y) == b`.
  - `x == y == z` is a chain, as in Dafny.
  - In axioms and lemmas, `if φ then ψ` without `else` is `φ ==> ψ` at the
    top. In [teq.dfy](resources/cuvee/teq.dfy) it is written with a line
    break before `then`.
- **The lemma database** [teq.dfy](resources/cuvee/teq.dfy) is injected by
  `-teq`.
  - Its sections after the first one are marked as needing manual checking.
  - Functions that produce traces are plural (`sums`, `maxs`, `counts`),
    their scalar counterparts singular (`sum`, `max`, `count`).
  - `counter(i, c, n)` is the trace `i, i + c, ..., i + n c`. The old Boogie
    `teq.bpl` had `counter(n)` = `counter(0, 1, n)` and
    `range(i, c, n)` = `counter(i, c, n)`.
  - Lemmas taken from there need explicit bounds (`0 <= k < n`, equal
    lengths, `distincts(keys)`), which the old file left implicit or got
    wrong.
- **Matching in rules** respects binders. A rule variable never captures a
  bound variable of the expression, so `map(for xs yield v => c)` only
  matches constant bodies.
- **Preludes.** Each language has one `resources/cuvee/<lang>/prelude.*`,
  whose declarations are attributed with the languages they are part of
  (`{:dfy}`, `{:bpl}`, `{:smt2}`, `{:c}`). They are parsed into the initial
  state and injected into the stream. The implicit last step
  (`transform/Language.scala`) drops what is part of `config.language`.
  Transforms therefore see the prelude's declarations, e.g. `Monomorph` must
  ignore the generic `=`. Tests that call a `Source` directly must drop
  `Examples.prelude(...)`.
- **Stages buffer declarations.** A `Stage` passes pending declarations to
  the sink as a batch, and `Sink.query(cmds, last)` reports only the answers
  to queries. So the sink's answer to a declaration (an error, `Unsupported`)
  is lost behind a stage. A filter that must keep those answers is a sink
  wrapper (like `Language.sink`), not a stage.
- **Normal forms and the context.** `Simplify.implied` and `denied` look facts up
  syntactically, and also by the negation in normal form (`not`). When a
  helper changes the normal form (e.g. `not` turns `!(a < b)` into
  `b <= a`), make sure facts are still found. Check the diff of
  expected outputs for simplifications that got weaker, not only stronger.
- **Pretty printing.** A parenthesized document must be wrapped in
  `Align(...)`, otherwise its line breaks nest relative to the enclosing
  indentation and operators end up left of their opening parenthesis. Check
  long outputs (e.g. `-verify` on `examples/dafny/vcgen/sum.dfy`) after
  printer changes.
- **Checking that a new test catches a bug:** stash only the fix
  (`git stash push <file>`), not the test, and run the test alone with
  `mill -i test.testOnly <suite>`.
- **Transient mill failures:** a crash inside the mill launcher (stack trace
  ending in `MillLauncherMain`) is not a test failure. Rerun.
- **Names the user mentions may refer to counterparts.** E.g. "teq.bpl"
  for the repository's `teq.dfy`. Check which files exist before assuming.
- **Rules with guards below combinators.** A bound variable of a pattern
  that occurs only in guards (`b` in `if b then y + 1, if !b then y`) is
  instantiated by matching the guard syntactically, not by implication. Such
  a variable also matches a negation, so put the lemma with the more
  specific guard (`!b`) first.
- **Testing lemmas of teq.dfy.** Inputs cannot use the trace functions
  before `-teq` injects them. Test rules on core terms with
  `Simplify.rules(TEQ.lemmas)` and `Rewrite`.
- **Expected values in unit tests** must be in the simplifier's normal form,
  e.g. `x - 1` becomes `x + -1`, and `j < j` collapses whole formulas.
- **Statements without effect** are the empty block (`Simplify.skip`), which
  `block` drops; a block of one statement without locals is that statement.
- **Commits with unrelated changes in the tree:** the version bump commits
  all tracked changes, so stash the unrelated files first.
- **The context is not a complete record of the siblings.** Below `ite`
  (the other branch), `let`, `match`, `all` (the dependencies), and neutral
  positions, parts of the formula are missing from `Ctx`. Anything that
  concludes from "x does not occur in the context" (the one-point rule) must
  forget its information there (`Ctx.opaque`).
- **Derivatives hide variables.** `Diff(xs, e)` is not free in the primed
  variables `x'` that its derivative introduces; `Ctx.used` adds them. The
  hybrid example with z3 caught this.
- **No solvers on polymorphic input.** Never run z3 (nor `-monomorph` as a
  workaround) on inputs with polymorphic definitions or axioms, e.g. anything
  with `-hybrid`. The tests of hybrid programs only generate the goals
  (`-print null`). Type annotations in Dafny are written `e as T`.
- **Helpers used as decisions** (e.g. `eq_(...) == True` in `distinct`,
  `select`, `deps`) get `ctx.neutral`, so that position-dependent rules do not
  fire there.
