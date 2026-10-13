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
| `src/cuvee/prove/Canon.scala` | the canonical renaming of the bound variables of a position, the keys of the memos |
| `scripts/prove/quick.sh`, `slow.sh` | the quick check after each change, the slow sets on request |
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
| P8 | the harness: `scripts/prove/quick.sh` (the state examples except the transpose, four per-variable examples, under 30 s), `scripts/prove/slow.sh` (the transpose, the unit tests, the 30 algorithms in the state form as a baseline), `scripts/prove/compare.sh` (`-prove` against `-simplify` on the per-variable examples without `-teq` modules) | done; the `teq:nested` difference explained (see the log) |
| P9 | the cost of the simplex: the checks cached by the set of constraints and disequations (`Linear.checks`, per command); with P10 the transpose takes 6.8 s instead of 22 s, the quick check 27 s instead of 36 s | done |
| P10 | canonical forms (package B): the bound variables of a position renamed by position (`Canon.renaming`), the memos of the views, the reads and the combinator facts keyed by the canonical facts and holding canonical values; the equations of variables are facts now, so the facts determine the classes; the canonical form of terms (`Canon.term`: inner binders numbered by depth, dependencies and cases in a fixed order, conjuncts and equations sorted), by which closed conditions with binders are looked up among the facts after both are normalized under the classes (`Rewrite.known`, `Classes.normalize`) and terms with binders are equal in `eq_`; 6 unit tests | done |
| P11 | triggers and forward facts (package J): step 1, `{:fw}` lemmas, done; step 2, `invs` instances, open; the pin in the matcher (E), exit splitting (K), diagnostics (M) | in progress |
| P12a | interim file in examples/dafny/state: bsearch.dfy with its expected output (no goal since J; bsearch_cut.dfy removed, the cut is not needed), which the test suite picks up; kept as a regression test with no goal, next to bsearch_sorted.dfy (the full version, in the paper) | note |
| P12 | the algorithms in the state form: binary search done (its bounds as forward facts, no goal), the views no longer recomputed; merge and the sorts open | in progress |
| S7 | combinators with several accumulators in the core (branch `accumulators`, from `prove`): `Trace(inits, deps, accs, bound, results)`, `Component(S, i)` and `History(S, i)` as core nodes, typed structurally over the existing sorts (`Trace<tupleₘ<...>>`); the Dafny grammar, parser (`trace(e₁, e₂, for ... do x, y, k :: u₁, u₂)`, `current(S).i`, `⌊S⌋.i`) and printer; `StateTEQ` emits the form per strongly connected component (S5); the engine of `-prove` handles traces of several accumulators (the views as syntactic projections, `self` a list of pairs); the other printers, the Lean printer, the fallback and `-simplify` handle single-accumulator traces only (`Trace.single`) | done Oct 13, 2026 |
| P13 | `-fallback` for tuple traces and the Lean printer, the tuples declared for C input under `-teq-state`, the C benchmarks of the state form with a cleaned-up lemma selection | deferred until the engine is in a reasonable state; benchmarks only when the user asks |

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

## Next steps, in order (revised Oct 13, 2026, evening)

The consolidated plan is [deduction-engine-plan.md](deduction-engine-plan.md) (its sections 1.2, 1.4 and 3); in
short:

1. (done) S5 and S7: traces per strongly connected component, emitted as traces of one or several accumulators,
   and the engine of `-prove` on their components (branch `accumulators`).
2. (done, step 1) J: forward facts, `{:fw}` lemmas fired at the terms of assumed facts; binary search closes without
   the cut. Next: which lemmas of the database should be `{:fw}` rather than `{:rw}` (with the user); step 2, the
   `invs` instances on the same triggers.
2a. (done, Oct 13) The binary search in `doc/state-traces`, the version over a sorted array only.
2b. (done, interim, Oct 13: `bsearch_sorted.dfy`, in two layers, 45 s; the bisection over the cycle, package O, next)
   The full binary search: sortedness as a predicate (`sorted(a, n)`, a quantified hypothesis) in place of the
   partition points p and q of the interim example, which are stronger than sortedness and turn the reads of the array
   into index comparisons by ground rules; the bounds of lo and hi then have to come from the monotonicity of the array.
2c. (done, Oct 13) O: the bisection over the cycle, a lemma with a pattern of two accumulators (the matcher's part
   of S6), its conditions over the guards decided by the rules on sortedness; bsearch_bisect.dfy in 11 s without the
   monotone layer (bsearch_sorted.dfy, the two layers, kept for now), lower_bound.dfy closes (8 s).
2d. Open items, unordered, as of Oct 13, 2026 (0.44.4):
   - which lemmas of the database should be `{:fw}` rather than `{:rw}`, a review led by the user;
   - step 3 of J: forward lemmas on traces fired where a trace is defined, with a memo per lemma and canonical
     term; the repeated firing at the same terms, needed only by the two layers of bsearch_sorted.dfy, goes with that
     version;
   - the bisection (`bisection`, `cut`, `bisection_lo`, `bisection_hi`) and the partition points of sorted arrays
     (`lower`, `upper`, `equal`, `bounds`, `cut_lower`, `lower_succ`) as a module of the database, now that
     bsearch_bisect, bsearch_safe and lower_bound share them; waits for the user;
   - step 2 of J: the `invs` instances at reads;
   - is_sorted under `-teq-state -prove` ends in "rewriting does not terminate" (already in 0.44.3; it left one
     goal earlier);
   - bounds of `quot`, C's truncating division (`half_2` of SV-COMP, the halving loops of
     [iterator-profiles.md](iterator-profiles.md)): those of `div` for `0 <= t`, a split by the sign otherwise;
   - the eight algorithms whose lemmas are missing from the state module (`count`, `distincts`, `maxs`): counting_sort,
     count_occurrences, distinct, first_duplicate, max_element, merge, partition, three_way_partition; the one goal
     of each of bubble, cocktail, gnome, insertion (two), selection sort, lower_bound, perm, reverse, transpose.
3. S6: the merge and the sorts in the partitioned form; lemmas over whole cycles (patterns with several accumulators)
   in the matcher; the pin (E), exit splitting (K), renaming (D) as they ask.
4. The rest of S7: the Boogie and SMT-LIB frontends and printers, the Lean printer and `-fallback` for traces of
   several accumulators; with S8.
5. S8, deferred: the fallback encoding, the tuples for C input, the C benchmarks with a cleaned-up lemma selection;
   benchmarks only when the user asks.

## Log (continued)

- **Oct 13, 2026, evening: S7 begun** on the branch `accumulators` from `prove` (1e17a69a and fae14245). The core
  data structures of section 1.4 of the plan: `Trace(inits, deps, accs, bound, results)` with `Trace.apply` for a
  single accumulator and the extractor `Trace.single`, the nodes `Component(trace, i)` (`current(S).i`) and
  `History(trace, i)` (`⌊S⌋.i`), typed by `Trace.components` of the element type, `Trace.elem` building the tuple
  type for several accumulators; `Expr.map`, `Subst`, `Type.expand`, `Type.check` (initial values and results against
  the accumulators, the components' types from the resolved trace type), `State.exprs.trace` with several accumulators.
  Dafny: `Combinator(kind, inits, deps, bound, updates)`, the grammar `trace(e₁, ..., eₘ, for deps do accs, bound ::
  u₁, ..., uₘ)` where each initial value ends with a comma (a list separated by commas would commit to an expression
  before `for`) and each result is guarded cases or a plain expression, the member access `.i` on `current(S)` and
  `butlast(S)` of a trace with several components resolved to the nodes; the printer prints several initial values on
  their own line. Boogie, SMT-LIB and Lean printers, `Fallback`, and both engines match `Trace.single` and pass traces
  of several accumulators through (the engines) or reject them (the printers), as the cheap workaround for now.
  `examples/dafny/state/accumulators.dfy` (two lemmas, one over the state of the swap) parses, type-checks and prints,
  and the printed output parses back identically; the quick check is unchanged.
- **Oct 13, 2026, night: S5 and S7 done.** `StateTEQ` partitions the loop's variables by the strongly connected
  components of the read relation (results, plus the guards if there are several paths; `util.SCC`), one trace per
  component in dependency order, a single accumulator for a variable in no cycle and several for a cycle, the
  histories of the earlier components as dependencies (`⌊X⌋`, `⌊S⌋.i`), the constraint over all histories; nested
  loops closed as before. The swap gives `I` a plain counter, `S` the two arrays over `⌊K⌋, ⌊I⌋`, `T` after them. The
  engine of `-prove`: the markers are `Component` and `History` nodes, their views the syntactic projection
  (`Views.project`: the component's accumulator alone, the others bound over `⌊S⌋.j`, which are inert dependencies, so
  the projections do not unfold each other), suspension by loop and component, replacement in place once the view
  reads no component, `self` a list of pairs (`⌊X⌋`, each `⌊S⌋.j`, the own history of a projection by position,
  `Views.selfOf`, `Views.relation`); the tuple-selector machinery, the `own` replacement and `Context.projection` are
  gone, `Simplify.once` handles `Trace` generally and `Component`/`History`. All ten state examples and
  `accumulators.dfy` check against their outputs; the swap closes with 160 rewrites and 16 views (262 before), the
  binary search takes 12 s (17 s), the cut variant 7 s (75 s), each with the one goal of the exit as before; the
  transpose 3 s. Open: lemmas over whole cycles (patterns with several accumulators) in the matcher, forward facts
  for the exit of the binary search (J), the other frontends, Lean and the fallback.
- **Oct 13, 2026, night: the projection folded into the matcher.** A pattern of the shape `current(trace(...))` or
  `⌊trace(...)⌋` is matched against a read `current(S).i`, `⌊S⌋.i` structurally, against the syntactic projection
  without simplifying it (`Views.structural`, tried after the definitions and before the normal form); the normal form
  of a component stays explicit and memoized, since folding a component into `stores` or evaluating its counter is a
  rewriting, not a match. Views computed: unchanged on the swap (16) and the binary search (64), since the lemmas that
  need the normal form dominate; the binary search 7 s instead of 12 s; quick check green.

## How to run

```
mill -i assembly; cp out/assembly.dest/out.jar cuvee.jar
./Cuvee.sh -teq-state -print dfy examples/dafny/state/swap.dfy      # the joint trace as a goal
./Cuvee.sh -teq-state -prove examples/dafny/state/swap.dfy          # the engine
./Cuvee.sh -teq-state -prove -debug rewrite examples/dafny/state/swap.dfy
mill -i test.testOnly cuvee.test.prove.*
scripts/prove/quick.sh      # after each change, under 30 s
scripts/prove/slow.sh       # on request or before a commit: the transpose, the unit tests, the algorithms in the state form
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
- **Oct 13, 2026, later.** The harness as `scripts/prove/quick.sh` (27 s) and `slow.sh`; the plan revised (canonical
  forms moved up, see the adjustments). `Canon`: the bound variables of a position renamed by their position, the
  memos of the views, the reads and the combinator contexts keyed by the canonical facts and storing canonical
  values (the combinator memo now holds the facts of the inner context, from which the context is built at each
  position, which also carries the suspension of the position); the equations of variables are stored as facts, so
  that the facts determine the classes; the simplex checks cached by the set of constraints (`Linear.checks`). The
  transpose 22 s to 6.8 s, the quick check 36 s to 27 s, nothing lost. First baseline of the 30 algorithms in the
  state form (slow.sh, the `-teq` modules dropped since the database is fresh), with the local lemmas of the files
  kept: 9 close without any lemma of theirs (fragments, inner_loop_flat, invs_counter_equation, invs_fragments,
  lsearch, nested_counter, nested_mult, nested_sum, row_sums), 7 leave one goal (argmax 7 s, gnome_sort 22 s,
  is_sorted, lower_bound 43 s, perm, prefix_sums, transpose 9 s, whose lemmas are written for the per-variable
  fragments), 5 time out at 60 s (bubble_sort, cocktail_sort, insertion_sort, insertion_sort2, selection_sort), 8
  fail since their lemmas use functions of the `-teq` modules that `state.dfy` lacks (count, distincts, maxs:
  counting_sort, count_occurrences, distinct, first_duplicate, max_element, merge, partition, three_way_partition),
  reverse exhausts the steps. Then `Canon.term`, the canonical form of terms, for the lookup of closed conditions
  with binders and for `eq_` (package B complete in the comparison sense; the matcher is modulo AC as before).
  The nested_sum and bubble_sort differences under `-teq -prove` with `teq:nested` traced: in a combinator context
  the simplifier chains a bound variable to its read first (`K₉ == earlier(natural(k), K?)`, from
  `Simplify.iterations`), so the later fact `K₉ == counter(0, 1, n₇)` is never followed and `counter_def` cannot
  fire inside the constraint; `prove` tries every member of the class and it fires. The lemmas of the module `nested`
  are written for the `sums` form that results from the simplifier's limitation, so the per-variable form with
  `teq:nested` is not a target of `-prove`; the comparison of the two engines (`scripts/prove/compare.sh`) leaves
  out the examples that include a module of `-teq`.
- **Oct 13, 2026, binary search in the state form** (P12, from examples/dafny/teq/bsearch.dfy with its partition
  points and its `incs`/`decs` abstractions, without the duplicated declarations). It timed out at first; the stack
  samples showed the hashing of terms (the state trace repeated throughout the goal by the closed substitution) and
  the ordering of canonical forms by the printed form. Changes: the compound expressions of the core cache their hash
  (`Expr.hashCode`, lazy); the canonical forms order terms by hash; the classes detect clashes on merge instead of by
  a scan; the lookup of closed conditions compares canonical forms only with facts of the same shape; and the
  outermost loops keep their definitions as equations (`Path.depth`, `StateTEQ.system(closed = depth > 0)`), since
  the engine follows them through the classes and the goal stays small, while nested loops stay closed (an inner loop
  must be a value of the outer update). Then the `incs`/`decs` lemmas did not match the views: (1) their other
  dependency is typed `List<int>` for the per-variable form, where it was `⌊Lo⌋`, but in the state form it is the
  list of states, so lemmas over other dependencies must be polymorphic in that type (`hs: List<a>`,
  `C: (int, a) -> bool`), as `invs_current_counter_other<a>` already is; (2) the relation of a projection (the own
  component read from the state is the accumulator) must reach the context of the update, both in the traversal and in
  the matcher, and cannot be carried by names, since `once` renames the binders of a trace while the rewrite at the
  top runs in the outer context: the context carries the selector being projected (`Context.projection`) and the
  relation is derived positionally from each trace (`Views.relation`, the second bound variable of the state's type),
  and `Simplify.invariants` replaces the read by the accumulator in the invariants over ⌊S⌋ and assumes the equation.
  With these, `incs` and `decs` fire on the views (81 and 94 times in a run), the index component needs `consts_def`
  in `state.dfy` (a trace that keeps its value, otherwise `incs` matches it with its other cases unspecified), and the
  exit needs the bounds `lo <= p`, `q <= hi` as in the per-variable proof (the cut, with `current_1`/`current_2` as
  rules on the views). Diagnostics added on the way: `-debug conditions` (closed conditions that fail, with the facts
  on their variables) and `-debug match` (trace patterns that fail on a trace, the uncovered case, the failing guard).
  Then the view recomputation: `-debug views` showed 397 memo misses with 233 distinct fact sets for the `lo` marker
  alone, since the key held all facts of a position and the sibling conjuncts differ everywhere. A view is now
  simplified under the facts that mention a variable of the view only (the state trace, the counter, the constants of
  the update; `Context.restricted`) and memoized by exactly those, which is sound; judging relevance by the view's
  variables rather than the marker's drops the facts about the marker's own bound variable as well. Misses 397 to 72,
  binary search from the 60 s timeout at the start to 17 s, the transpose from 22 s this morning to 2 s; nothing lost
  on the quick check. The variable-definition fallback now matches through views (`a == S.1(current(S))` reaches the
  bound lemma on the view), which closes the found case of the cut; the exit case of the cut remains open since the
  sibling conjuncts turn `lo <= p` into `lo == p` before the bound rule sees the comparison, and `-split` leaves two
  goals: this is the forward-facts item (package J): the bounds of a named trace should become facts when the term
  occurs. The split pipeline is not pursued further. Binary search is left here: one goal without the cut (the
  exit), two with `-split`.
- **Oct 13, 2026, night: J, step 1.** `{:fw}` lemmas (`Forward`): the trigger is the term of the conclusion below
  its boolean, comparison and arithmetic structure with the most variables; fired by `Forward.assume` where the
  traversal assumes facts (the premise and the denied conclusion of an implication, the siblings in `nary`), matched
  through definitions and views like rules, the conditions decided like those of rules, the instance stated over the
  term as it occurs; instances assumed by `Context.assume` (generation 1), no firing while matching a trigger, known
  instances skipped. The binary search in the state form closes with `current_1`, `current_2` as `{:fw}` (the
  `incs_`/`decs_` workaround removed): 16 instances each, 7 s as before, no goal. Quick check unchanged (24 s).
  Not done: firing at the decision of an atom (the denied conclusion covers the examples), the memo of matches per
  trigger and canonical term (not needed so far), the static check of new terms (needed only for step 2).
- **Oct 13, 2026, night: the binary search over a sorted array, and N.** `bsearch_sorted.dfy`: `sorted(a, n)` and
  the partition points `lower`, `upper` as functions with rules on the reads within `a[0..n)`; the range of the
  midpoint in the update needs `0 <= lo` and `hi <= n` there, which forward lemmas on monotone traces give as `invs`
  over the histories (`up_1`, `down_1`, trigger the history `⌊S⌋.i`, matched through its view); then `incs` and `decs`
  match with the partition points as bounds. Engine: `Forward.terms` descends into the dependencies of combinators,
  the trigger is a term rather than a formula among equals, the firing repeats at the same terms while instances are
  added (the bounded abstractions match only after the invariants), instances checked by their conjuncts (the
  conjunctive conclusions were never known and looped); the views keep the facts over the variables of the view and
  of their definitions only (364 misses to 199, 68 s to 48 s); the `-debug` lines no longer print `self` pairs as
  equations (a type mismatch). N: division by a positive literal bounded in `Linear.add`, which retires the midpoint
  lemmas (`lemma_4`, `lemma_5` of bsearch.dfy) and brings the sorted search under the step budget (about 450 of
  1000 steps, 46 s). The two layers are the cost: the invariant is a joint one, hence O (a bisection lemma over the
  cycle) next, then step 3 of J (firing at definitions with a memo), which replaces the repeated firing.
- **Oct 13, 2026, night: O, the bisection over the cycle.** The matcher matches a pattern of several accumulators
  against a trace of as many, component by component, the results in the context of the update with the histories of
  the matched variable as `self` (so `lo < hi` of the iteration constraint holds there); a read `current(T).i`,
  `⌊T⌋.i` of a pattern matches that of a variable through its definition; lambdas match lambdas. The lemmas
  `bisect_1`, `bisect_2` (forward facts at `current(S).0`, `current(S).1`): a bisection of `[l0, h0)` whose guards
  `G((hi + lo) / 2) && lo < hi` and `H(...)` hold on a prefix and a suffix (closed quantified conditions, decided by
  the rules on sortedness within their range) keeps `l0 <= lo <= cut(G, l0, h0)` and `cut((j: int) => !H(j), l0, h0) <= hi <= h0` (one cut for both ends,
  `lower(a, n, x + 1) == upper(a, n, x)` for the negated guard);
  the cuts are rewritten to the partition points by rules with a lambda on the left, which needed the forward
  instances simplified before they are assumed. `P` and `Q` cannot be variables of the lemma: a variable that only a
  quantified condition mentions is not bound by matching facts. bsearch_bisect.dfy closes in 11 s with 282 log
  steps, against 45 s for the two layers of bsearch_sorted.dfy, which is kept for now with the repeated firing it
  needs; lower_bound.dfy, open under `-simplify`, closes in 8 s.
- **Oct 13, 2026, night: the bisection named, with a probe.** One `cut` for both ends (`cut((j: int) => !H(j), ...)`,
  `lower(ar, len, y + 1) == upper(ar, len, y)` since `!(y < ar[j])` normalizes to `ar[j] < y + 1`). The trace is named
  by a rule `bisection(l0, h0, ks, M, G, H)` and bounded by two forward lemmas on `current(bisection(...)).i`, with a
  probe `M(lo, hi)` and the condition `forall l, h :: l < h ==> l <= M(l, h) < h`, decided by the division bounds.
  Engine: equations of traces of several accumulators rewritten with their variable as self (the iteration constraint
  in the update of the match), component reads matched through the other definitions of the variable when the trace
  does not match, instantiated arguments of higher-order patterns beta-reduced (`G(M(lo, hi))`), and a higher-order
  pattern not yet instantiated may take several summands when the sum does not match otherwise
  (`M(lo, hi) + 1` against `lo + (hi - lo) / 2 + 1`). bsearch_bisect 8 s, bsearch_safe (the probe
  `lo + (hi - lo) / 2`) 10 s, lower_bound 8 s; the lemmas lose the suffix `_def` (lower, upper, equal, bisection), and
  the note on naming the variables of lemmas apart from the goal's moved to doc/teq.md. The paper waits until the
  approach has converged.
- **Oct 13, 2026, night: the state form is `-teq`.** `-teq` produces the state form (`StateTEQ` always), `-teq-state`
  and the per-variable `TEQ.system` are removed; the database entry is `resources/cuvee/teq.dfy`, the former
  `teq/state.dfy`, the former single file of the per-variable form backed up in `resources/cuvee/legacy/teq.dfy`;
  the optional modules stay for a reorganization. The 63 examples with `-teq` outside examples/dafny/state run
  `-prove` in place of `-simplify` (outputs regenerated): the C examples and most Dafny ones as before, 14 algorithms
  and four Dafny examples fail on functions and lemmas of the former modules (`count`, `distincts`, `maxs`,
  `consts_prefix` of `teq:nested`, the higher-order lemma on distinct keys of affine), is_sorted does not terminate
  as before. Errors of injected modules are reported like parse errors (no stack trace). The two unit tests of the
  rewriting of `-simplify` on lemmas of the former database parse `legacy/teq.dfy`; quick.sh without the
  per-variable examples, compare.sh removed; the benchmark definitions run `-prove` without the optional modules.
- **Oct 13, 2026, night: one form.** `StateTEQ` folded into `TEQ` (`TEQ.system`), the term "state form" dropped from
  the code and the docs (examples/dafny/state keeps its name); the database migration begun with `core.dfy`
  (ideas/teq-modules.md).
- **Oct 13, 2026, night: aggregation and arithmetic migrated** (ideas/teq-modules.md, progress); forward lemmas fire
  when a comparison or equation is decided at a position with a polarity (`Simplify.forward`), for bare goals.
