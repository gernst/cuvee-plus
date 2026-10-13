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
  traced. Nothing committed yet.
