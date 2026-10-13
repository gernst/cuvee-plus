# Trace equation systems

Verification by symbolic execution and trace equation systems (TEQs), after
*Trace Equation Systems for Program Verification*. Loops are summarized by
equations over traces, which the engine of `-prove` rewrites with a lemma
database until the goal is proved ([prove.md](prove.md)). SMT solvers are not expected to solve TEQs: there
are no special cases for traces in the solver interface, no implicit
monomorphization, and no implicit introduction of TEQ concepts to the solvers.

## Combinators ([Expr.scala](../src/cuvee/core/Expr.scala))

```scala
case class Upd(cond: Expr, rhs: Expr)                         // if cond then rhs
case class Eps(updates: List[Upd])                            // some rhs whose cond holds
case class Trace(inits: List[Expr], deps: List[Expr], accs: List[Var], bound: List[Var], results: List[Expr])
case class Maps(deps: List[Expr], bound: List[Var], update: Expr)
case class Invs(deps: List[Expr], bound: List[Var], body: Expr)
case class Component(trace: Expr, index: Int)                 // current(S).i
case class History(trace: Expr, index: Int)                   // ⌊S⌋.i
```

After section 3 of the paper, generalized to several accumulators
([ideas/deduction-engine-plan.md](../ideas/deduction-engine-plan.md), section 1.4):

- `Trace(inits, deps, accs, bound, results)` is the trace of the accumulators
  `accs`, one initial value and one result each, of type `Trace(T)` for a
  single accumulator and `Trace((T₁, ..., Tₘ))` for several, where the tuple
  type names the state and no term of tuple type is ever built. It starts
  with `inits`; each further value is the results of the previous ones and
  the next values of the dependencies, which `bound` ranges over point-wise.
  `Trace.apply(init, deps, acc, bound, update)` builds the single case and
  `Trace.single` matches it; the lemma database, the lowering of `-fallback`,
  the Lean printer and the printers of Boogie and SMT-LIB handle that case
  only. Several accumulators are for the variables of a loop that depend on
  each other (a cycle of the read relation), whose per-variable traces would
  be recursive through each other.
- `Component(S, i)` is the component `i` of the last value of a trace of
  several accumulators, `History(S, i)` the list of its earlier values, of the
  ordinary type `List(Tᵢ)`: the history of such a trace is `m` lists, which
  are dependencies like any other, so `Maps` and `Invs` are unchanged and the
  functions on lists apply. Both are typed by the component types of the
  trace (`Trace.components`); the type checker resolves the type of the
  trace first.
- `Maps(deps, bound, update)` is the sequence of the updates, of type
  `Seq(T)`.
- `Invs(deps, bound, φ)` states `φ` for all values of the dependencies.
- The dependencies are always sequences (`Seq(T)`), at least one, all of the
  same length (`Type.dependencies`), e.g. `⌊K⌋` of a trace `K`. Their length
  is `Seqs.len` of the theory of sequences (not `Fun.trace.length`). A trace
  with `n` steps has `n + 1` elements: the `n` of `⌊X⌋`
  (`earlier(0..n-1, ⌊X⌋)`) and `current(X)`. The goals contain no lengths:
  the number of iterations `n` is that of the counter `K == counter(0, 1, n)`
  of the iterations, and the lemmas iterate over counters, whose length `n`
  they use directly.
- An update is an expression: a single result, or guarded cases
  `Eps(List(Upd(φᵢ, eᵢ), ...))` with disjoint and complete guards, a variant
  of Hilbert's choice. The parsers build `Eps` only for written guards, the
  simplifier flattens nested `Eps` (`Eps.flatten`), merges cases with equal
  results by the disjunction of their guards, and replaces a single case by
  its result, since the guards are complete. The guards need not be
  complete since `break`; an update without cases, e.g. when all guards are
  false, is a value that is not specified, the constant `unspecified` of
  `core.dfy` (`Unspecified`). `List[Upd]` has `free`, `params`, and
  `map` like lists of expressions.
- The functions on traces are in `Fun.trace`: `counter`, `current`, `butlast`
  (the paper's `⌊X⌋`), `length`, `earlier`; `Counter`, `Current`,
  `Butlast`, `Earlier`, and `Length` in
  [Builtin.scala](../src/cuvee/core/Builtin.scala) are their sugar. The sort is `Sort.trace(elem)`.
- `state.exprs.trace`, `map`, and `all` create the bound variables with the
  element types of the dependencies (`Type.elem`); `trace` with lists of
  initial values and accumulators builds a trace of several.

## Syntax

| Combinator | Dafny and Boogie | SMT-LIB |
|---|---|---|
| `Trace` | `trace(e, for Y, Z do x, y, z :: u)` | `(trace (x e) ((y Y) (z Z)) u)` |
| `Trace`, several accumulators | `trace(e₁, e₂, for Y do x₁, x₂, y :: u₁, u₂)` (Dafny only; the first bound variables are the accumulators, as many as initial values) | not supported |
| `Component`, `History` | `current(S).1`, `⌊S⌋.1` (Dafny only) | not supported |
| `Maps` | `maps(for Y yield y :: u)` (Boogie: `map(...)`) | `(map ((y Y)) u)` |
| `Invs` | `invs(for Y check y :: φ)` (Boogie: `all(...)`) | `(invs ((y Y)) φ)` |
| update | `case φ₁ => e₁ case φ₂ => e₂` | `(eps (φ₁ e₁) (φ₂ e₂))` |

`⌊X⌋` is `butlast(X)` in Dafny and Boogie.

## The transform `-teq` ([TEQ.scala](../src/cuvee/verify/TEQ.scala))

`TEQ` replaces each procedure definition by a goal from symbolic execution,
after section 4 of the paper; with an entry point (`-entry`, or `main` in C,
see `Config.entryPoint`) only that of the entry point, since calls are inlined,
which checks the other procedures in the context of their calls, and not for
arbitrary arguments (e.g. `sanfoundry_24-1`, whose `printEven` holds only for
the even numbers that `main` passes).

- A `Path` holds the fresh variables for nondeterministic choices, the values
  of the variables as a substitution, and the assumptions, branch conditions,
  and checks along the way. Choices `if *` become branches on fresh booleans,
  calls are inlined, which requires procedures without a contract (e.g. C
  functions) and does not terminate for recursive ones.
- Each loop yields a single path (theorem 4.8), which assumes its trace
  equation system (definition 4.4, partitioned as below): one `Trace` per
  strongly connected component of the modified variables, whose updates have a
  case per path through the body, the counter
  `K = counter(0, 1, n)`, and the iteration constraint `Invs`, and which
  checks that the body executes safely from the current state. Its exits
  (by the negated test, and by `break` or `return` in a last iteration from
  the current state) are told apart by branch conditions, not assumptions:
  an enclosing loop guards the cases of its updates by the branch conditions
  of the paths (`Upd(q.B, ...)`), which must be disjoint; with the exit
  conditions as assumptions, two exits with different values gave
  contradicting cases, from which any goal followed
  ([teq_nested_break.c](../examples/c/verify/teq_nested_break.c), the
  `*_unwindbound*` tasks, whose `while (counter++ < k)` is `while (true)`
  with a `break`).
- A loop whose body ends by `break` or `return` on all paths runs it at most
  once: its body is a conditional on the test, without a trace equation
  system, where `break` continues after the loop.
- The goal is that all checks hold and the postcondition follows on every
  path.
- Differential equations and parallel composition are not supported; loop
  invariants are ignored.

## The partition into components

`-teq` partitions the modified variables of a loop by the strongly connected components of their read
relation (`TEQ.system`, `util.SCC`): a variable reads the variables in its
results and, if the paths are guarded, in the guards, which all results share. The components are ordered so that
each comes after those it reads, and each becomes one trace: a trace of a single accumulator for a variable in no
cycle, as in the paper, and a trace of several accumulators for a cycle (see Combinators above), with the counter,
the histories of the earlier components it reads (`⌊X⌋`, `⌊S⌋.i`) and the choices as dependencies. The exit values
are `current(X)` and `current(S).i`, the iteration constraint ranges over the counter and all histories. Since the
component graph is acyclic, no trace depends on another one, and the system of a nested loop is closed
(`Path.depth`): the counter, the traces and the exit values are substituted by their definitions, such that only the
number of iterations and the choices are fresh, and an inner loop is a value of the outer update rather than a
family of fresh sequences; an outermost loop keeps its definitions as equations, which the engine follows on demand.
All singletons is the per-variable form of the paper, which is exactly the case where that form had no cycles; the
per-variable form for every loop, the former `-teq`, was removed on Oct 13, 2026, when the partition, until then
`-teq-state`, became `-teq`. The lemma database is
[teq.dfy](../resources/cuvee/teq.dfy). The
per-variable traces of a cycle are projections of its trace that the engine of `-prove` computes on demand (see
[prove.md](prove.md)), and a rule may also match the trace of a cycle as a whole, with a pattern of several
accumulators, e.g. the bisection of the binary searches, which names the trace of `lo` and `hi`; the simplifier of
`-simplify` does not know traces of several accumulators. Examples in
[examples/dafny/state](../examples/dafny/state), the design in
[ideas/deduction-engine-plan.md](../ideas/deduction-engine-plan.md), the implementation in
[ideas/deduction-engine-implementation.md](../ideas/deduction-engine-implementation.md).

## The lemma database ([resources/cuvee/teq](../resources/cuvee/teq))

- The database is [teq.dfy](../resources/cuvee/teq.dfy), its entry point, which
  `-teq` injects (`TEQ.modules`, `Config.injected`): the types `Nat`, `List`,
  `Trace`, the functions of `Fun.trace`, the functions on lists that the lemmas
  need, and the lemmas about traces, started as the module `state.dfy` of
  `-teq-state` with the lemmas of [examples/dafny/state](../examples/dafny/state).
  The optional modules of [resources/cuvee/teq](../resources/cuvee/teq) are
  injected on demand by `-include teq:<concept>`, after it. They were written
  for the per-variable form (until Oct 13, 2026, `-teq` injected `core`,
  `arithmetic`, `counters`, `aggregation`, `arrays`, `search` in this order,
  and `nested`, `sorting`, `strides` were optional); they are migrated file by
  file into modules over teq.dfy alone (see
  [ideas/teq-modules.md](../ideas/teq-modules.md)). `core.dfy`, the
  declarations and the definitions that several modules share, is migrated:
  teq.dfy has all of them (`sum`, `parity`, `max`, `min`, `count`, `pow`,
  `distincts`, `selects`), the file is in `legacy/`; so are `aggregation.dfy`
  (`-include teq:aggregation`: counts, maxima, minima, the linearity of sums,
  indicators) and `arithmetic.dfy` (`-include teq:arithmetic`: the rules that
  the arithmetic of `-prove` does not decide on its own), migrated as modules
  over teq.dfy. The others still declare
  functions that teq.dfy declares as well, or refer to each other, and cannot
  be included with teq.dfy until they are migrated. What they hold: `counters.dfy`
  `mods(i, c, m, n)`, the counter modulo `m` of the unsigned variables of C,
  whose arithmetic wraps around (`mods_def`), with lemmas that bound it by the
  tests of loops below `m` (not proved in `teq.lean` yet); `teq:nested` the
  fragments of inner loops (the inner counter, its final value, its iteration
  constraint, its exit stated on the constraint fragment
  `invs(for ks, Ns check k, nn :: integer(nn) <= n)`, the numbers of inner
  iterations as `⌊consts(m, natural(n))⌋`, the outer trace of a variable that
  only the inner loop modifies, `results`), which `-teq` no longer needs,
  since an inner loop is a value of the outer update; `teq:sorting` (`sorted`,
  `perm`, `partitioned`, inductions); `teq:strides` (the strided stores and
  stores ahead of the MonoCera benchmarks, see
  [benchmarks/monocera](../benchmarks/monocera), which fix the number of
  stores and of cases on their left-hand sides, are not proved in
  `teq.lean`, and are not tested). The order of the modules is the order in
  which the rules are tried.
  [legacy/teq.dfy](../resources/cuvee/legacy/teq.dfy) is the former single
  file of the per-variable form, from which its modules were split: a backup,
  not injected. The database is printed as Lean by including the modules
  without `-teq`, which
prints them since the feature is not known to the output:
  `./Cuvee.sh -known dfy -print lean -include teq:core -include teq:arithmetic ... empty.dfy`.
- Injected by the source with `-teq`, after its prelude (`Config.features`):
  Dafny input parses it with its own parser, such that the input can refer to
  its declarations, other input with a fresh Dafny parser; the TEQ transform
  relies on it. It defines the datatype `Trace`, declares the functions on traces,
  and lemmas about them, which are `{:rw}` (rewrite rules of `-prove`) or `{:fw}` (forward lemmas) and
  free, without a body (assumed by the solvers without proof). Lemmas that
  identify a trace with a function of the database are named after it, e.g.
  `stores_def` (likewise `selects_def` for `maps`, `agree_prefix_def` for
  `invs`), those about an accessor of such a function after both, e.g.
  `current_sums` or `earlier_prefix`, the others after what they state,
  e.g. `current_trace_two_phases` or `sum_add`.
- `Trace` exists only with `-teq`. Inputs that use traces without `-teq`
  declare `Trace` themselves; Dafny inputs with `-teq` use the declarations of
  the database, inputs in other languages cannot.
- Within a module, the function declarations come first, then the lemmas,
  grouped by the function of their left-hand side (the combinator, `current`,
  `prefix`, ...). Rules are tried in the order of the modules and of the
  files, lemmas whose order matters keep it within their group.
- Functions that are traces are defined by them with `{:fold}`, whose rule
  folds such a trace into the function (`stores`, `sums`, `selects`, ...);
  these definitions stand among the lemmas, at the position of their rule.
- Functions that produce traces are plural (`sums`, `maxs`, `counts`), their
  scalar counterparts singular (`sum`, `max`, `count`).
- Lemmas found on the SV-COMP examples (`benchmarks/sv-comp/dafny`) are merged into
  the groups, with the examples they come from as `(from ...)`, and two new
  groups, the length of iterations and arithmetic in the normal form of the
  simplifier. Left out are lemmas that are no rules in general: the split of
  a trace on a fixed condition, which loops; `!(y % 2 == 0) <==> y % 2 == 1`,
  which changes the normal form of guards and loops with the joins of guarded
  stores; comparisons of two open variables as left-hand sides, e.g.
  `n <= b`, which match every comparison; the joins of two guarded stores
  into one store of a conditional value, since a pattern with two cases
  also matches an update with a single case, leaving the variables of the
  other case unbound (see TODO.md), and the join at the position of a
  further dependency also exhausts the rewrite steps; and lemmas that never
  match. The examples keep these lemmas locally.
- A second merge (2026-10-10) added arithmetic (`triangle_nonneg`,
  `half_4x_4xx`, `div_below`, ...), reads over updates at other positions
  (`select_store_other`) and beyond a search (`select_not_occurs_selects_beyond`),
  bounds of sums under the auxiliary predicates `below_prefix` and
  `nonneg_prefix`, and counters with a step (`indexof_counter_step`,
  `prefix_maps_counter`). A merged lemma is checked by re-running the tasks
  whose local copies it replaces, which must reproduce their rows of
  `benchmarks/sv-comp/dafny/expected.csv`, and by its proof in teq.lean. This
  showed further lemmas that stay local:
  - the definition of an auxiliary predicate by an iteration constraint with
    a general body, `invs(... :: x <= b) <==> below_prefix(n, xs, b)`, since
    it matches the bound of every loop, `x < N` as `x + 1 <= N` with the body
    generalized to a map, and hides it from the lemmas on traces
    (`diamond_1-1`); the predicate and its consequences are in `aggregation.dfy`, the
    definition is local (`linear-inequality-inv-*`), unlike definitions with
    a specific body such as `consts_prefix_def`;
  - `!(y % 2 == 0) <==> y % 2 == 1` again, which opened
    `simple_array_index_value_1-1`;
  - lemmas on maps of a counter with a further dependency that the body does
    not use, and with the body `c - k`, which `a + b * v` of
    `maps_counter_affine` does not match as `N + -k + -1`
    (`array_init_both_ends_multiple_sum`).
- Auxiliary predicates abstract iteration constraints, e.g. `agree_prefix`
  and `consts_prefix`, and are defined by recursion over the positions,
  `earlier(m, xs)`, which teq.lean proves their lemmas with; their names avoid
  those that inputs declare with other meanings, since equal signatures are
  identified.
- An iteration constraint is never a side condition. Deciding one matches it
  against the `invs` facts of the context (`Rewrite.conditions`), which builds
  the simplifier's context of each such fact (`Simplify.combinator`) and
  rewrites the reads of its dependencies there; if a read produces the
  left-hand side of the rule again, the rule recurs through the same fact
  until the step budget is exhausted: `sum_invs_const`, now
  `sum_consts_prefix`, had the left-hand side `sum(js)`, which matched the
  `sum(prefix(...))` that `earlier_sums` makes of the read of a trace of sums
  (see TODO.md). Such a rule is not decreasing in the sense of conditional
  rewriting, since its condition is not smaller than its left-hand side; since
  0.42.3 the run terminates (the rule is suspended while its condition is
  matched, and the reads of a context are normalized by the rules without an
  `invs` condition, [simplifier.md](simplifier.md)), but the rule still does
  not apply, since the read it would match is not rewritten while it is
  suspended. Instead, a definition lemma abstracts the constraint by an atom, e.g.
  `consts_prefix_def`:
  `invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(natural(k), js) == c) <==> consts_prefix(n, c, js)`,
  and the lemma that needs the constraint takes the atom as its side
  condition, e.g. `sum_consts_prefix`, which is matched against the facts
  syntactically. The body of the definition lemma reads the sequence
  explicitly, `earlier(natural(k), js)`, with a further dependency `hs` for
  those of the constraint: a bound variable `j` of a dependency `J` of the
  constraint matches the read through its equation
  `j == earlier(natural(k), J)` in the context of the combinator, as do an
  explicit read and the symmetric equation `c == j`, while `c` must not
  capture `k`, so values that depend on the iteration, `j == k + 1`, do not
  match, nor does an equation without a read, `x == 5` for a variable `x` of
  the context. The values of a trace match too, so
  `invs(for ⌊K⌋, ⌊X⌋ check k, x :: x == 5)` becomes `consts_prefix(n, 5, ⌊X⌋)`,
  which hides the constraint from `Simplify.invariants`, since that collects
  `invs` facts only; a definition lemma therefore comes late among the lemmas
  on `invs`, after those that use such constraints.
- Lemmas written for a program (the summaries of inner loops, the inductions,
  the chains of [examples/dafny/algorithms](../examples/dafny/algorithms),
  whose NOTES.md records the findings) follow patterns that the matcher
  imposes:
  - **Variables named apart.** The variables of a lemma are named apart from
    those of the goal, i.e. of the method and its context: a variable of a
    rule with the name of a variable of the goal captures it, e.g. a lemma
    variable `n` that occurs only in its condition is then taken as the
    goal's `n` and the match leaves it unbound ("variables of a rule not
    instantiated"). The binary searches of
    [examples/dafny/state](../examples/dafny/state) write their lemmas over
    `ar`, `len`, `y` for the method's `a`, `n`, `x`.
  - **Specific left-hand sides.** A left-hand side `invs(...)` whose body has
    a bare bound variable of a variable dependency on one side, `n <= j` or
    `j == integer(nn)`, matches every comparison, respectively equation,
    fragment, since the dependency is synthesized as a map of the fact's
    dependencies (`Rewrite.instantiate`); with an `invs` side condition such
    a rule cycles. A function symbol on the side of the bound variable,
    `integer(nn) <= n`, `J == counter(0, 1, nn)`, or an atom is specific.
  - **Fresh variables for every `invs` side condition.** A side condition is
    open while it has a variable that no earlier condition bound; an open one
    is matched against the facts, with backtracking over them, a closed one
    is decided by the simplifier, which does not find a closed `invs` among
    the facts (these carry unused dependencies, e.g. the counters of the
    outer loop, which the simplifier also drops from the instance, and their
    bound variables are renamed). So each `invs` condition binds a fresh
    sequence, `invs(for ks, js6, Js6 check k, j, J :: j == current(J))`, and
    an equation `js6 == js4 && Js6 == Js3` identifies it; the equation is
    closed and decided trivially. The 21st condition of the cocktail sort's
    summary stayed closed for a day.
  - **Open trace variables.** The traces of the goal are variables `K`, `R`
    with their equations as hypotheses; `⌊counter(0, 1, m)⌋` as an argument
    of a left-hand side never matches `⌊K⌋` (as a dependency of a combinator
    it does, through the context). A rule takes `Kv == counter(0, 1, m)`,
    `Rv == results(false, ⌊Kv⌋, rs)` as open conditions, matched against the
    hypotheses, and uses `⌊Kv⌋` afterwards.
  - **A condition on the rule's own left-hand side term** is admissible since
    0.42.3: the instance of a condition is simplified before it is decided or
    matched, and a condition `l == current(Lv)` of a rule on `current(Lv)`
    with `Lv` bound rewrote `current(Lv)` by the rule itself without end;
    the rule is suspended while its conditions are evaluated
    (`Context.active`, [simplifier.md](simplifier.md)). The summaries took
    `current(results(...))` as left-hand side rather than `results(...)` for
    this reason, and lower_bound.dfy stays open for another (its summary leaves
    the dependency variables unbound, TODO.md).
  - **Arithmetic conditions in the goal's form.** The decision procedure
    combines difference constraints; `len <= 2 * integer(m) + 1` is not
    decided from `n <= integer(m) + lo + 1` and `lo == integer(m)`, while
    `l == integer(m)` (open, matched) and `len <= integer(m) + l + 1` (the
    fact) are.
  - **The exit of an outer loop.** In the goal it is a disjunction in the
    conclusion, `i < n && !r || post`, which `-split` does not split and whose
    literals a rule on an atom of `post` does not see; a postcondition stated
    as two implications gives each goal its literal (first_duplicate.dfy).
    The exit of an inner loop is a fragment and a side condition like the
    others.
  - **Summaries are tied to the fragment forms of the included modules**
    (`j == current(J)` without `teq:nested`, `j == k + integer(nn)` with it),
    so a file includes the modules its lemmas are written for.
  - **Diagnostics.** Truncated copies of a summary with its first k
    conditions find the first failing one; *probes*, rules with the real
    left-hand side, the first k conditions and a fresh atom `probe_k(...)` as
    right-hand side, k downwards, show in the goal the largest k whose
    conditions hold; pair runs of the single lemmas of a module find a
    cycling pair; every result is checked on a program with a wrong
    postcondition, which must leave a goal; long runs use a private copy of
    the jar and read the exit status, since a killed run prints no goal.

## The semantics in Lean ([teq.lean](../resources/cuvee/teq.lean))

- `Trace` is a datatype of `core.dfy`, a value followed by the trace of the
  remaining iterations (`step`) or a last value (`stop`), hence never empty,
  with `current` and `butlast` defined by recursion; teq.lean takes them
  from the printed `core.dfy`. The functions that the database only declares are
  defined in Lean 4 (core, without Mathlib): `current`, `butlast`, `counter`,
  and `consts` are recursive; sequences are lists;
  the auxiliary predicates (`agree_prefix`, ...) are the iteration
  constraints that they abstract.
- There is a single combinator of each kind, `trace`, `maps`, and `invs`,
  defined by recursion over one dependency, `trace` as a right fold; the Lean printer zips several
  dependencies, `List.zip d₁ (List.zip d₂ d₃)`, binds their values by a
  tuple, `fun acc ⟨b₁, b₂, b₃⟩ => ...`, and prints guarded cases as
  conditionals. Zipping truncates to the shortest dependency, the lengths
  are not assumed yet (see TODO.md).
- The functions that the modules define with `{:fold}` and the lemmas are
  printed by `-print lean`, the lemmas as theorems, whose statements are
  copied into teq.lean when lemmas are added, and proved there.
- Checked counterexamples show lemmas that hold only under assumptions that
  the contexts of the goals provide, e.g. `n ≥ 0` or dependencies of equal
  length.
- Check with `lean resources/cuvee/teq.lean` (Lean 4.34); teq.lean is built
  from the output of `-print lean` on the modules (see above) and
  the hand-written definitions at its beginning.
- The dependencies of a combinator have equal lengths, which `zip` in Lean
  does not assume: `-print lean` adds hypotheses on the lengths to each
  lemma (`lean.Printer.lengths`), `(hxs : length xs = n)` for each list
  variable that is a dependency of a combinator, also through a `{:fold}`
  function, or that is read at the iterations `k` of a counter by
  `earlier(natural(k), xs)`, where `n` is the number of steps of a counter
  among the dependencies or a further parameter `(n : Nat)` of the lemma;
  `length` is declared in `core.dfy` with `{:lean}` as `List.length` of Lean.
  With them, all lemmas of teq.lean are proved; assumptions on indices
  within the lists are added by hand there as `requires` to be added to
  the module. teq.lean proves 164 of the 205 lemmas of the database: those of
  `arithmetic`, `aggregation`, `arrays`, and `search`, and 50 of the 62 of
  `counters`; the lemmas of `nested`, `sorting`, and `strides` are not in
  teq.lean yet.
- A new lemma of a module goes into teq.lean by printing the module with
  `-print lean` and copying its statement (as a theorem) and those of new
  functions, at the position it has in the database, then proving it. The printer
  cannot see the length of a list that is no dependency of a combinator but
  is summed or read under an auxiliary predicate, e.g. `sum(xs)` under
  `below_prefix(n, xs, b)`: such lemmas hold for lists of length `n` only and
  get `(hxs : length xs = n)` by hand (`sum_consts_prefix`,
  `sum_below_prefix`, `earlier_nonneg_prefix`, `sum_nonneg_prefix`), listed in
  the header of teq.lean.

## The fallback encoding `-fallback` ([Fallback.scala](../src/cuvee/transform/Fallback.scala))

After section 5.3 of the paper, `-fallback` lowers the goals into first-order
logic for solvers, e.g. `-teq -prove -split -prove -fallback -z3`;
nothing polymorphic remains of the lemma database, hence no `-monomorph`.
Traces of several accumulators are not lowered yet (S8 of
[ideas/deduction-engine-plan.md](../ideas/deduction-engine-plan.md)): a goal
with a cycle that `-prove` leaves open is rejected.

- The variables of traces and lists bound by universal quantifiers of
  positive polarity, e.g. of `∀ xs. φ ⇒ ψ`, or by existential ones of
  negative polarity become uninterpreted functions of an integer index,
  with a fresh index, since the goals of `-split` share variables; those of
  other quantifiers are errors.
  A trace `X` of `n` steps has the entries `X(0), ..., X(n)`, `current(X)`
  is `X(n)`, `⌊X⌋` the same function below `n`; `earlier(k, ⌊X⌋)` is
  `X(k)`. Naturals become integers, `natural(x)` is `x` if nonnegative and
  0 otherwise.
- The length of all dependencies of a combinator is the `n` of its first
  one, `⌊counter(0, 1, n)⌋`, written directly or by an equation
  `K == counter(0, 1, n)` among the hypotheses of the quantifier
  (`Fallback.hypotheses`), which hold for all of its body, as in the context
  of the simplifier: the antecedents of implications, the conjuncts of
  hypotheses, and the formulas of negative polarity of disjunctions, e.g. of
  `¬(φ ∧ ψ)`, which the simplifier makes of `φ ∧ ψ ⇒ false`, but not those
  of a single conjunct of a goal; lists among the dependencies of equations
  and iteration constraints get it as well; those whose length follows
  from no hypothesis, e.g. the nondeterministic choices of a loop that the
  simplifier has eliminated, get a fresh length, as the functions are
  universal. Counters are inlined, their
  entries are `i + j * c`.
- A list of traces, e.g. the traces of an inner loop per iteration of the
  outer one, is a function of two indices, `K(j, i)`, with a function for the
  length of each trace, `K_length(j)`; a bound variable of a combinator that
  ranges over it is the trace at `j`, whose equations, e.g.
  `K' == counter(0, 1, n')`, also state its length `K_length(j) == n'`.
- The equations `X == trace(...)`, `maps(...)`, or of functions defined with
  `{:fold}` (unfolded) become their characterizations,
  `X(0) == e && ∀ j. 0 <= j < n ==> (φᵢ ==> X(j + 1) == eᵢ)`, one
  implication per case, since the guards need not be complete (`break`);
  `invs` is `∀ j. 0 <= j < n ==> φ`.
- Combinators that are not equated to a variable are fresh functions of
  their free variables, defined in the antecedent of the goal, where the
  traces among them contribute the free variables of their lowered
  functions and lengths, e.g. the `n` of `K == counter(0, 1, n)`
  (`Fallback.arguments`), likewise for generalized terms. Equal terms share
  their function if their traces and lists are lowered alike (`Fallback.key`),
  not, e.g., `map(for ⌊K'⌋ yield ...)` for the traces `K'` of a list of
  traces at different positions. `consts(n, v)` and `prefix(k, xs)` state
  their lengths, `nil` has length 0, e.g. the iterations of an inner loop
  that runs zero times, other traces and lists get a
  fresh length function.
- The definitions of the lemma database by a `match` on a parameter of type `List` or
  `Nat`, with a case per constructor, whose other case recurs on the tail or
  the predecessor only, with the other arguments unchanged (`sum`, `parity`,
  `count`, `occurs`, `pow`, `agree_prefix`, `above_iterations`), are unfolded
  once per position (`Fallback.recursion`): over a list `xs` of length `n`,
  a fresh function `f_from(j)` for the suffix from `j`, with
  `f_from(n) == base` and `f_from(j) == step(xs(j), f_from(j + 1))`, and
  `f(xs)` is `f_from(0)`; over a natural `n`, `f_upto(0) == base` and
  `f_upto(k + 1) == step(k, f_upto(k))`, and `f(n)` is `f_upto(n)`. This
  follows the definitions of the lemma database without restating them.
- The other functions of the lemma database, e.g. `indexof` and `distincts`, which
  also apply `occurs` to the tail, and those of the input without a
  definition are replaced by fresh functions without definition,
  which generalizes the goal: a model of the solver need not be a
  counterexample.
- The declarations and lemmas of the lemma database and lemmas over traces, lists,
  and naturals are dropped.
- Tests: [fallback.dfy](../examples/dafny/teq/fallback.dfy),
  [fallback_count.dfy](../examples/dafny/teq/fallback_count.dfy),
  [fallback.c](../examples/c/teq/fallback.c),
  [fallback_negated.c](../examples/c/teq/fallback_negated.c),
  [fallback_nested.c](../examples/c/teq/fallback_nested.c),
  [fallback_recursion.dfy](../examples/dafny/teq/fallback_recursion.dfy).

## Simplification and rewriting

- The simplifier's helpers `trace`, `maps`, and `invs`
  ([Simplify.scala](../src/cuvee/simplify/Simplify.scala)) collapse equal
  dependencies (by `eq_`), renaming their bound variables to the first one,
  and drop dependencies whose bound variables are unused, except counters
  `⌊counter(...)⌋`; the first one is kept if none remains, since the
  dependencies must be nonempty. `invs` with a constant body is `true` or
  `len(dep) == 0`. Guards and results of `Eps` are simplified, results
  under their guard and, since the guards are disjoint, the negations of the
  other guards, and cases with guard `false` are dropped. The guards are not
  simplified under the negations of the others: as the guards are also
  complete, each would become `true`.
- `invs` distributes over conjunctions, `invs(for Y check y :: φ && ψ)` is
  `invs(for Y check y :: φ) && invs(for Y check y :: ψ)`, each with the
  dependencies it uses.
- The updates of `trace` and `maps` and the body of `invs` assume the
  invariants among the assumptions of the context whose dependencies are
  among their own (`Simplify.invariants`), with the bound variables renamed
  to those of the same dependencies. The positions coincide, since the
  dependencies of a combinator have equal length.
- If the first dependency counts the iterations of a loop,
  `⌊counter(0, 1, n)⌋` (also through a variable `K == counter(0, 1, n)`)
  bound to `k`, they also assume `0 <= k < n`, since the loop exits when
  `k == n`, and `z == earlier(k, ⌊Z⌋)` for each other dependency `⌊Z⌋`
  bound to `z` (`Simplify.iterations`).
- The rewrite engine ([Rewrite.scala](../src/cuvee/simplify/Rewrite.scala))
  matches the binding structure of the combinators: dependencies of the
  pattern are selected among those of the expression (`bound` of
  `Rewrite.matches` relates the bound variables), and dependencies that are
  variables of the rule are instantiated by `Maps` expressions. Each case of the expression's update is
  covered by a case of the pattern, whose guard matches syntactically (which
  instantiates bound variables that occur only in guards, e.g. `b` in
  `if b then y + 1`) or whose conjuncts follow from the guard of the
  expression or match its conjuncts (`Rewrite.conditions`). Variables of
  the left-hand side that a match leaves unbound occur only in cases of the
  pattern that cover no case of the expression, which never apply, since the
  cases of the expression hold in all iterations by the iteration
  constraints; they are instantiated by `unspecified`, e.g. `c` of
  `case D(k, h) => c` of `current_trace_flag` for an update without the case
  of a `return` where `D` holds. Other unbound variables are reported as an
  error of the rule (`Rewrite.apply`).

## Tests

- `examples/dafny/vcgen/*.dfy` without loops must generate their goals with
  `-teq` (never passed to a solver).
- `examples/c/teq/*.c` and `examples/dafny/teq/affine.dfy` state their command
  line, e.g. `-teq -split -prove`, and the goals that remain in their
  expected output (none if they are proved).
- [TEQ.scala](../test/src/cuvee/test/dafny/TEQ.scala) checks the goals of
  `-teq`, the injection of the database, and the lemmas on core terms
  (`Rules.from(State.empty, TEQ.lemmas)` with `Rewrite`).
- [RewriteTraces.scala](../test/src/cuvee/test/simplify/RewriteTraces.scala)
  tests the rewrite engine with the examples of the paper (counters,
  summations, `selects`) in single steps; `examples/dafny/simplify/traces*.dfy`,
  `dependencies.dfy`, and `invariants.dfy` the simplifier and the rewrite rules on
  traces, which declare `Trace` and the functions on traces as in `core.dfy`.
- E.g. `./Cuvee.sh -teq -prove examples/dafny/vcgen/sum.dfy`.
- The Dafny translations of SV-COMP (`benchmarks/sv-comp/dafny`) and the C
  programs printed from them (`benchmarks/sv-comp/c`, since patched for other
  verifiers, which `expected.csv` predates) have databases of their
  expected results (`expected.csv`, suites `SVComp` and `SVCompC`, only with
  `CUVEE_SVCOMP`), recorded one process per task with 60 s under the former
  per-variable form with `-simplify` (to be recorded again under `-teq -prove`,
  which `test/Database.scala` now runs); their summary is
  `benchmarks/sv-comp/dafny/summary.md`. The translations write the division
  and remainder of C as `quot` and `rem` of the prelude of Dafny, lemmas keep
  `/` and `%`. `-print c -known dfy,teq,rw` prints their programs without
  the logic, where `teq` keeps the lemmas of the database out of the output;
  the C programs lack the lemmas of their Dafny files, hence they leave goals
  that the Dafny files close (see TODO.md).
