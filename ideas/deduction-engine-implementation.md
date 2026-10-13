# Implementing the deduction engine: the package `prove`

The working record of the implementation of [deduction-engine-plan.md](deduction-engine-plan.md), started Oct 13,
2026 on the branch `prove` of the main checkout (not a worktree). It holds the instructions of the user, the design
decisions taken, the state of each step and a log of progress, such that the work can be picked up at any time.

## Instructions (Oct 13, 2026)

Verbatim in substance, from the user:

- Start implementing the deduction engine plan from the best understanding of the plan; start from scratch, on a new
  branch in the main filesystem, re-using the insights as well as code from the branch `worktree-state-trace`
  (commit b6f2b969) as seen fit. The plan is documented in `ideas/`; ask to revise the plan if substantial changes
  seem necessary.
- Work in a new package `prove`. Ideas and code snippets may be borrowed from `simplify`, but by copying them: the
  package `prove` is independent of `simplify` and does not reference it.
- Only the variant of `TEQ.scala` that builds the modified equation system goes to `transform`. That code exists on
  the branch (`TEQ.stateSystem`, a datatype per loop); change it to work with the tuples of the Dafny prelude instead.
- Work with a clean and fresh setup of the trace database, as done on `worktree-state-trace` (the single module
  `state.dfy`); branching off from there and re-using its flag (`-teq-state`) is allowed.
- Do not re-run the entire test suite. Keep experiments to TEQ-related ones, plus potential small unit tests for the
  new functionality.
- Consider the command line flags: `-include` to inject additional definitions, and a new flag `-prove` that runs
  the new engine, like `-simplify` runs the simplifier.
- Instead of Floyd-Warshall (the difference constraints of the simplifier), rely on a stronger arithmetic solver.
- Document progress by periodically reporting back, and write the instructions and the progress into this file.

## Decisions

- **Branch.** `prove`, from main at 8c720e86 (which has the re-entrance guard and the test gating), not from
  `worktree-state-trace` (based on 7b2d316f): the pieces of that branch are copied over instead, so that the
  simplifier of main stays as it is and the views live in `prove` only. Copied: `resources/cuvee/teq/state.dfy`,
  `examples/dafny/state/*` (command lines changed to `-prove`), the flag and `Config.stateTraces`, and the state
  form of `TEQ.loop`.
- **Where the state form lives.** `TEQ.scala` (package `verify`) keeps the symbolic execution and calls
  `cuvee.transform.StateTEQ.system` for the state form when `config.stateTraces` holds; the per-variable form stays
  in `TEQ`. `StateTEQ` builds the joint trace over the tuples `tupleₘ` of the Dafny prelude (constructor `tupleₘ`,
  selectors `tupleₘ_0`, ..., looked up in `state.datatypes`), with the closed substitution of the branch (the counter,
  the trace and the exit values are terms over the number of iterations and the choices, so an inner loop is a value
  of the outer update). A loop with one modified variable keeps the per-variable form, which is its own projection.
- **Markers.** With tuples, a selector no longer identifies the loop: the suspension of a view is keyed by the state
  trace term and the component index, not by the selector (the review's difference 4 is moot).
- **The arithmetic.** A simplex over the rationals (general simplex with bounds after Dutertre and de Moura, Bland's
  rule, strict bounds by an infinitesimal) replaces the difference constraints; on `Int`, strict comparisons are
  tightened to non-strict ones by 1 before they reach the solver, and bounds on single atoms are rounded. Facts are
  kept as a list of constraints and the tableau is rebuilt per check (memoized per context); incremental pivoting is
  a later optimization.
- **The context.** Congruence closure over the terms of the facts (a persistent union-find with congruence) in place
  of the chains: `Context.↑` becomes "the members of the class", which the matcher tries in order (the plan's
  packages F and G), a pattern variable matches a class, equal counters are identified, and the one-point rule stays
  as it is. The facts as given, the classes and the linear constraints are the theories.
- **Views.** As on the branch: a read of a component (a selector applied to the current or an earlier value of a
  state trace, or a map of one) is a marker that stays in place; a pattern that does not match it is matched
  against its simplified view (the per-variable projection); the component is not projected inside its own view
  (suspension); a marker whose view reads no component is replaced by it. Views are memoized by the marker, the
  dependencies and the classes of the context (not by the full context, the review's difference 5).
- **Suspension.** One facility for rules and views: `Context.active` holds the rules and the components being
  evaluated, by identity.
- **Closed conditions.** A closed instance of a side condition is looked up among the facts modulo the classes before
  it is decided by simplification (package C).

## Files

| file | contents |
|---|---|
| `src/cuvee/transform/StateTEQ.scala` | the joint trace of a loop over the tuples of the prelude, the closed substitution |
| `src/cuvee/verify/TEQ.scala` | the hook: `loop` builds the state form if `config.stateTraces` |
| `src/cuvee/Config.scala` | `-teq-state`, `-prove`, `stateTraces`, `TEQ.stateModules` |
| `src/cuvee/prove/Arith.scala` | polynomials (copied from `simplify.Arith`) |
| `src/cuvee/prove/Normalize.scala` | clauses (copied from `simplify.Normalize`) |
| `src/cuvee/prove/Rule.scala` | rules from lemmas and definitions (copied from `simplify.Rule`) |
| `src/cuvee/prove/Simplex.scala` | linear arithmetic over the rationals |
| `src/cuvee/prove/Classes.scala` | congruence closure |
| `src/cuvee/prove/Context.scala` | the sequent: facts, classes, linear constraints, bound variables, rules, suspension, memos |
| `src/cuvee/prove/Rewrite.scala` | matching modulo classes and views, side conditions looked up then decided |
| `src/cuvee/prove/Simplify.scala` | the traversal with the normalizing helpers, the contexts of combinators |
| `src/cuvee/prove/Views.scala` | the projections of state traces |
| `src/cuvee/prove/Prove.scala` | the transform of `-prove` |
| `resources/cuvee/teq/state.dfy` | the fresh database of `-teq-state` |
| `examples/dafny/state/` | the examples, `-teq-state -prove` |
| `test/src/cuvee/test/prove/` | unit tests of the simplex and the classes |

## Steps

| step | what | state |
|---|---|---|
| P1 | branch, this file, the flags, `StateTEQ` over tuples, the database and the examples copied | done |
| P2 | `prove`: polynomials, clauses, rules, simplex, classes, context | done |
| P3 | `prove`: the traversal, the matcher modulo classes, the combinator contexts, the transform `-prove` | done |
| P4 | `prove`: views of state components with suspension and memo | done |
| P5 | the single-loop examples (counter, copy, init, swap, lsearch) under `-teq-state -prove` | done, all close |
| P6 | the nested examples (nested_counter, nested_sum, nested_mult, row_sums, transpose) | done, all close |
| P7 | unit tests, docs (`doc/prove.md`, options, architecture, teq, CLAUDE.md, README), version 0.43.0 | done |
| P8 | the per-variable examples of `-teq` (examples/dafny/teq, examples/c/teq) under `-prove`, compared with `-simplify` | open |
| P9 | the cost of the simplex: incremental tableau or a cache of checks; the transpose at 22 s against 7 s | open |
| P10 | canonical forms (package B): bound variables numbered by position, so that `invs` conditions are looked up modulo renaming and the memos share contexts | open |
| P11 | triggers and forward facts (package J), the pin in the matcher (E), exit splitting (K), diagnostics (M) | open |
| P12 | the algorithms of examples/dafny/algorithms in the state form: bsearch (the views of `lo` and `hi` recomputed), merge, sorting | open |
| P13 | `-fallback` for tuple traces and the Lean printer, the tuples declared for C input under `-teq-state`, the 60 s C benchmarks of the state form | open |

## Adjustments to the plan (Oct 13, 2026, after the first milestone)

Against [deduction-engine-plan.md](deduction-engine-plan.md) as revised by [state-trace-review.md](state-trace-review.md):

- **The main line S1 to S4 is done in the form of the sketch**, not of the plan: the joint trace over tuples (S1),
  views in place of the projection rewrites and the derived equations (S2, S3), the closed substitution in place of
  ghost components (S4). S5 (tuple patterns in the lemma language) stays optional: the transpose's lemma is written
  with nested traces directly. S6 splits: the lowering of tuple traces by `-fallback` and the Lean printer are needed
  before any C benchmark of the state form, and the C frontend needs the tuples declared (the Dafny prelude has them,
  C has not: `StateTEQ` should declare `tupleₘ` ahead of the goal when the state lacks it, as the branch declared its
  datatypes); making `-teq-state -prove` the default is far off.
- **Package G landed as F plus transitivity, not as matching modulo classes.** A term may be matched by a member of
  its class only if the member does not contain it, otherwise the rewrite cycles (`a[k]` by `S.2[k] == a[k]`); the
  implementation restricts this to variables. Matching an arbitrary term modulo its class needs a term order on the
  members (a member is a definition if it is smaller or does not contain the term) or equality saturation (L), which
  rewrites nothing in place. G in the plan's full sense is therefore moved behind L, and the term-order variant is a
  small item on its own.
- **Package H (arithmetic over classes) changes shape.** With the simplex as the theory, the natural combination is
  the other way round: equalities that the bounds imply (`lo <= x <= lo`) are merged into the classes, and the
  solutions of linear equations stay inlined into polynomials as now. The classes do not need polynomial
  representatives.
- **Package A (the harness) is needed now, in a TEQ-only form:** the ten state examples, `-teq -prove` against
  `-teq -simplify` on examples/dafny/teq and examples/c/teq by the number of remaining goals, and the 30 algorithms in
  the state form; the full suite and the C benchmarks come with S6. The nested_sum difference under `teq:nested` is
  the first case for it.
- **The cost model.** The simplex rebuilt per check is affordable on the ten examples but visible (the transpose at
  three times the sketch); it belongs before the algorithms (P12), since those multiply the checks.

## Next steps, in order

1. P8, the harness: a script that compares `-prove` with `-simplify` by remaining goals on examples/dafny/teq and
   examples/c/teq, and runs the algorithms in the state form; the nested_sum difference traced.
2. P9, the simplex: an incremental tableau per context (assert bounds on the copy of the parent's tableau) or a cache
   of the checks by the constraint set.
3. P12, the algorithms in the state form, which is the real test of the representation: bsearch first (the views of
   `lo` and `hi` under guards, recomputed per context on the branch), then merge and the sorts; the module `state.dfy`
   grows by what they need, the engine by what the matcher lacks (the pin E, the one-point rule over sequences,
   triggers J), pulled by the examples rather than built ahead.
4. P13, S6 in parts: `-fallback` for tuple traces, the tuples declared for C input, then the 60 s C benchmarks of the
   state form against the per-variable form.
5. P10, canonical forms, once the `invs` lookups or the memo misses show up in P12.

## How to run

```
mill -i assembly; cp out/assembly.dest/out.jar cuvee.jar
./Cuvee.sh -teq-state -print dfy examples/dafny/state/swap.dfy      # the joint trace as a goal
./Cuvee.sh -teq-state -prove examples/dafny/state/swap.dfy          # the engine
./Cuvee.sh -teq-state -prove -debug rewrite examples/dafny/state/swap.dfy
mill -i test.testOnly cuvee.test.prove.*
```

## Log

- **Oct 13, 2026.** Branch `prove` created from main (8c720e86); this file; `state.dfy` and the examples copied from
  `worktree-state-trace`. `StateTEQ` over the tuples of the prelude, `TEQ.loop` calls it under `-teq-state`, the
  per-variable form moved into `TEQ.system`; the flags `-teq-state` and `-prove`. The package `prove` written:
  `Arith`, `Normalize`, `Rule` copied; `Simplex` (general simplex, 11 unit tests), `Classes` (congruence closure, 5
  unit tests), `Theory` (facts, linear constraints with solutions), `Context`; `Simplify` and `Rewrite` copied and
  adapted (definitions of variables through the classes, lookup of closed conditions, views, one suspension
  facility, programs and derivatives dropped); `Views` from the branch with the component key `(selector, number of
  iterations)` instead of the selector, since tuples share selectors across loops; `Prove`. Two bugs on the way: the
  accumulator of a projection must take the instantiated component type (the selector's result type is a type
  parameter), and a term may not be matched by a member of its class that contains it (`a[k]` by `S.2[k] == a[k]`
  from a sibling conjunct cycled), so only variables have definitions, as in the simplifier. The simplex needed the
  explicit check that no lower bound exceeds an upper bound. Result: all ten examples of examples/dafny/state close
  (1.5 to 22 s, the transpose slowest); the `-teq` examples checked by hand are unchanged (teq/swap, counter, bsearch,
  rules, c/teq/fallback, algorithms/nested_sum, simplify/reentrant_invs). Docs: doc/prove.md, options,
  architecture, teq, CLAUDE.md, README, the README of the examples; version 0.43.0. Not run: the full test suite.
  A first look at P8: under `-teq -prove` (the per-variable form, the full database) teq/counter, swap and bsearch
  close as under `-simplify`; algorithms/nested_sum with `teq:nested` leaves one goal that `-simplify` closes, to be
  traced. Committed as 8af7d753 on the branch `prove`.
