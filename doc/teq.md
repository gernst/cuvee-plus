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
([doc/prove.md](prove.md), section 1.4):

- `Trace(inits, deps, accs, bound, results)` is the trace of the accumulators
  `accs`, one initial value and one result each, of type `Trace(T)` for a
  single accumulator and `Trace((T₁, ..., Tₘ))` for several, where the tuple
  type names the state and no term of tuple type is ever built. It starts
  with `inits`; each further value is the results of the previous ones and
  the next values of the dependencies, which `bound` ranges over point-wise.
  `Trace.apply(init, deps, acc, bound, update)` builds the single case and
  `Trace.single` matches it; the lemma database handles that
  case only, the engine of `-prove`, the parsers and printers of Dafny, Boogie,
  SMT-LIB (and SV-LIB, whose terms are those of SMT-LIB), the Lean printer and
  the lowering of `-fallback` also several. Several accumulators are for the variables of a loop that depend on
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
  teq.dfy (`Unspecified`). `List[Upd]` has `free`, `params`, and
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
| `Trace`, several accumulators | `trace(e₁, e₂, for Y do x₁, x₂, y :: u₁, u₂)` (the first bound variables are the accumulators, as many as initial values) | `(trace ((x₁ e₁) (x₂ e₂)) ((y Y)) u₁ u₂)` |
| `Component`, `History` | `current(S).1`, `⌊S⌋.1` | `((_ current 1) S)`, `((_ butlast 1) S)` |
| `Maps` | `maps(for Y yield y :: u)` (Boogie: `map(...)`) | `(map ((y Y)) u)` |
| `Invs` | `invs(for Y check y :: φ)` (Boogie: `all(...)`) | `(invs ((y Y)) φ)` |
| update | `case φ₁ => e₁ case φ₂ => e₂` | `(eps (φ₁ e₁) (φ₂ e₂))` |

`⌊X⌋` is `butlast(X)` in Dafny and Boogie. In Boogie, `.1` scans as an
identifier, since the dot is a character of identifiers, which the grammar
accepts after an atom (`boogie.Grammar.access`). In Lean, a trace of several
accumulators is a trace of their product, `trace (e₁, e₂) Y (fun ⟨x₁, x₂⟩ y =>
(u₁, u₂))`, its components are selected from the nested pairs,
`(current S).2.1`, and its histories are `maps (butlast S) (fun s => s.2.1)`.

## The transform `-teq` ([TEQ.scala](../src/cuvee/verify/TEQ.scala))

`TEQ` replaces each procedure definition by a goal from symbolic execution,
after section 4 of the paper; with an entry point (`-entry`, or `main` in C,
see `Config.entry`) only that of the entry point, since calls of procedures
without a contract are inlined, which checks these procedures in the context
of their calls, and not for arbitrary arguments (e.g. `sanfoundry_24-1`, whose
`printEven` holds only for the even numbers that `main` passes).

- A `Path` holds the fresh variables for nondeterministic choices, the values
  of the variables as a substitution, and the assumptions, branch conditions,
  and checks along the way. Choices `if *` become branches on fresh booleans,
  calls of procedures without a contract (e.g. C functions) are inlined,
  which does not terminate for recursive ones, and calls of procedures with a
  contract are by the contract, as in `-vcgen` (`VCGen.instance`): the
  precondition is a check, the results and modified global variables are
  fresh, the postcondition an assumption.
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
accumulators, e.g. the bisection of the binary searches, which names the trace of `lo` and `hi`. Examples in
[examples/dafny/teq](../examples/dafny/teq) and [examples/dafny/algorithms](../examples/dafny/algorithms), the design in
[doc/prove.md](prove.md), the implementation in
[doc/prove.md](prove.md).

## The lemma database ([resources/cuvee/teq](../resources/cuvee/teq))

- The database is [teq.dfy](../resources/cuvee/teq.dfy), its entry point, which
  `-teq` injects (`TEQ.modules`, `Config.injected`): the types `Nat`, `List`,
  `Trace`, the functions of `Fun.trace`, the functions on lists that the lemmas
  need, and the lemmas about traces, started as the module `state.dfy` of
  `-teq-state` with the lemmas of the examples then in `examples/dafny/state` (since Oct 23, 2026 in
  [examples/dafny/teq](../examples/dafny/teq) and [examples/dafny/algorithms](../examples/dafny/algorithms)).
  The optional modules of [resources/cuvee/teq](../resources/cuvee/teq) are
  injected on demand by `-include teq:<concept>`, after it. They were written
  for the per-variable form (until Oct 13, 2026, `-teq` injected `core`,
  `arithmetic`, `counters`, `aggregation`, `arrays`, `search` in this order,
  and `nested`, `sorting`, `strides` were optional); they are migrated file by
  file into modules over teq.dfy alone (see
  [doc/teq.md](teq.md)), all but `nested` by
  Oct 13, 2026; rules that still iterate over the iterations and the loop
  variable, or over further variables `hs`, match the single dependency of
  `-teq` (see [prove.md](prove.md)). Migrated:
  `core.dfy`, whose declarations went into teq.dfy (`distincts`, `selects`)
  and into the modules of their concept;
  `aggregation.dfy` (`-include teq:aggregation`: the functions `sum`, `count`,
  `max`, `min`, `parity` and the traces `sums`, `parities`, `counts`, `maxs`,
  `mins`, with the linearity of sums, indicators and bounds);
  `arithmetic.dfy` (`-include teq:arithmetic`: `pow` and the rules that the
  arithmetic of `-prove` does not decide on its own, e.g. the exactness of the
  halved triangles, also with a coefficient); `search.dfy`
  (`-include teq:search`: agreeing prefixes, no occurrence, values above the
  iterations, with their facts at the reads as forward lemmas, and the
  bisection of an interval with a probe, `bisection`, `bisection_lo/hi`);
  `sorted.dfy`, formerly `sorting.dfy` (`-include teq:sorted`: `sorted`,
  `perm`, `partitioned`, inductions, and the partition points `lower`, `upper`
  of a sorted array with their bounds); `arrays.dfy` (`-include teq:arrays`:
  stores at a counter and at distinct keys, conditional stores, resets, the
  reads of an array updated along a trace); `counters.dfy`
  (`-include teq:counters`: phases, flags, catching up, merged cases, constant,
  increasing and bounded values, the remainders of phases that add a constant); and `strides.dfy` (`-include teq:strides`:
  the strided stores and stores ahead of the MonoCera benchmarks, see
  [benchmarks/monocera](../benchmarks/monocera), which fix the number of
  stores and of cases on their left-hand sides); and `unsigned.dfy`
  (`-include teq:unsigned`: `mods(i, c, m, n)`, the counter modulo `m` of the
  unsigned variables of C, whose arithmetic wraps around, with the bounds of
  its iteration constraints below `m` and its final values); and
  `series.dfy` (`-include teq:series`, after `teq:aggregation` and
  `teq:arithmetic`, whose `sum` and `pow` it uses: the folds `squares`,
  `cubes`, `fourths`, `fifths` of the sums of the powers of a counter from
  `i`, with their coefficients taken out and Faulhaber's formulas times their
  denominators as forward facts in a variable `c == integer(n)`, the halved
  triangles that `sum_counter` leaves and the powers of `integer(n)` in `c` as
  well, and the
  geometric sequences and the fold `series` of geometric series, Oct 23,
  2026). The forward facts of `series.dfy` are triggered at its folds, not at
  general terms such as a sum over a counter or the current value of a trace:
  such a trigger is tried at every matching term and slows down the tasks it
  does not apply to, even without an instance (zero_sum4: 857 instead of 193
  rewrites, until the bound on the steps is exhausted). Each of its forward
  lemmas is one equation, since the engine splits a forward lemma at its
  conjunctions and triggers each conjunct on its own: a conjunct
  `integer(n) * integer(n) == c * c` would be triggered at every
  `integer(n)` (in-de61.1 and in-de62.1 of SV-LIB in 0.50.15). The rules of
  these files never applied on SV-COMP and specific to one task were left
  out; they were dropped with the legacy database on Oct 23, 2026.
  Retired on Oct 14, 2026 (and removed on Oct 23): the former `teq:nested`, the fragments of inner loops (the inner counter,
  its final value, its iteration constraint, its exit stated on the constraint
  fragment `invs(for ks, Ns check k, nn :: integer(nn) <= n)`, the numbers of
  inner iterations as `⌊consts(m, natural(n))⌋`, the outer trace of a variable
  that only the inner loop modifies, `results`), which `-teq` no longer needs,
  since an inner loop is a value of the outer update; the nested sorting
  algorithms leave the same goals without it. The order of the modules is the order in
  which the rules are tried.
  The former single file of the per-variable form, from which the modules
  were split, was kept as a backup until Oct 23, 2026. The database is printed as Lean by
  [scripts/lean/generate.py](../scripts/lean/generate.py), which concatenates
  the modules into one file and prints it with `-print lean` (with `-teq`, the
  output hides the database).
- Injected by the source with `-teq`, after its prelude (`Config.features`):
  Dafny input parses it with its own parser, such that the input can refer to
  its declarations, other input with a fresh Dafny parser; the TEQ transform
  relies on it. It defines the datatype `Trace`, declares the functions on traces,
  and lemmas about them, which are `{:rw}` (rewrite rules of `-prove`) or `{:fw}` (forward lemmas) and
  free, without a body (assumed by the solvers without proof). A function
  that is a trace or a map is a fold (`{:fold}`, below) rather than a
  declaration with a lemma `<name>_def` (Oct 23, 2026: `mods`, and the
  predicates that abstract iteration constraints, `agree_prefix` and
  `above_iterations`, folds of their constraints). A `_def` lemma remains
  where the function cannot be its own fold: `counter_def` (the counter is the
  iteration of its own definition) and `consts_def` (over a counter of any
  start and step, which a fold, whose variables are its formals, does not
  abstract). A lemma that rewrites into a function without defining it is
  named after what it states, e.g. `counts_true` (a trace of booleans),
  `stores_cases`, `sorted_adjacent`, `not_occurs_prefix`; those about an
  accessor of a function after both, e.g. `current_sums` or `earlier_prefix`,
  the others after what they state, e.g. `current_trace_two_phases` or
  `sum_add`.
- A lemma that at most three proved tasks of SV-COMP apply says so on its
  `(from ...)` line, `used on SV-COMP by <tasks> only` (the union of the
  results of Cuvée since Oct 13, 2026, counted by `-rules`, see
  scripts/rules.py), and a lemma that none applies, `unused on SV-COMP`, with
  the reason why it stays (a law of a function of the database, a pair of a
  used lemma, the examples); the lemmas of `sorted` serve the examples only
  (module header).
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
  A fold need not be a trace: `swap(a, p, q)` of sorted.dfy folds the two
  stores `a[p := a[q]][q := a[p]]`, such that the lemmas on swaps name the
  positions once each; its elements are `select_swap`, and lemmas of programs
  that include `teq:sorted` state their swaps as `swap(...)`, since the stores
  of the program are folded before they are matched.
- Functions that produce traces are plural (`sums`, `maxs`, `counts`), their
  scalar counterparts singular (`sum`, `max`, `count`).
- Lemmas found on the Dafny translations of SV-COMP tasks (removed on Oct 23, 2026) are merged into
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
  whose local copies it replaces, which must reproduce their results, and by its proof in Lean (lean/). This
  showed further lemmas that stay local:
  - the definition of an auxiliary predicate by an iteration constraint with
    a general body, `invs(... :: x <= b) <==> below_prefix(n, xs, b)`, since
    it matches the bound of every loop, `x < N` as `x + 1 <= N` with the body
    generalized to a map, and hides it from the lemmas on traces
    (`diamond_1-1`); the predicate and its consequences are in `aggregation.dfy`, the
    definition is local (`linear-inequality-inv-*`), unlike definitions with
    a specific body such as the fold `agree_prefix`;
  - `!(y % 2 == 0) <==> y % 2 == 1` again, which opened
    `simple_array_index_value_1-1`;
  - lemmas on maps of a counter with a further dependency that the body does
    not use, and with the body `c - k`, which `a + b * v` of
    `maps_counter_affine` does not match as `N + -k + -1`
    (`array_init_both_ends_multiple_sum`).
- Auxiliary predicates abstract iteration constraints, e.g. `agree_prefix`
  and `above_iterations`, and are defined by recursion over the positions,
  `earlier(m, xs)`, which the Lean proofs use; their names avoid
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
  `invs` condition, [prove.md](prove.md)), but the rule still does
  not apply, since the read it would match is not rewritten while it is
  suspended. Instead, a definition lemma abstracts the constraint by an atom, e.g.
  `consts_prefix_def`:
  `invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(natural(k), js) == c) <==> consts_prefix(n, c, js)`,
  and the lemma that needs the constraint takes the atom as its side
  condition, e.g. `sum_consts_prefix`, which is matched against the facts
  syntactically. The body of the definition lemma reads the sequence
  explicitly, `earlier(natural(k), js)` (a further dependency `hs` for those
  of the constraint, which these lemmas had, is not needed: the matcher ignores
  the dependencies of the expression that the pattern does not select, Oct 23,
  2026): a bound variable `j` of a dependency `J` of the
  constraint matches the read through its equation
  `j == earlier(natural(k), J)` in the context of the combinator, as do an
  explicit read and the symmetric equation `c == j`, while `c` must not
  capture `k`, so values that depend on the iteration, `j == k + 1`, do not
  match, nor does an equation without a read, `x == 5` for a variable `x` of
  the context. The values of a trace match too, so
  `invs(for ⌊K⌋, ⌊X⌋ check k, x :: x == 5)` becomes `consts_prefix(n, 5, ⌊X⌋)`,
  which hides the constraint from `Simplify.invariants`, since that collects
  `invs` facts only; a definition lemma therefore comes late among the lemmas
  on `invs`, after those that use such constraints. `consts_prefix_def` and
  `sum_consts_prefix` were dropped on Oct 23, 2026, never applied
  on SV-COMP: `consts_choice` of teq.dfy makes the constraint on a dependency
  the constant sequence `xs == ⌊consts(n, c)⌋`, whose sum is `sum_consts`,
  without the premise on the length of the list that the read `earlier(natural(k), js)`
  needed in Lean; definition lemmas of this form remain in search.dfy
  (the folds `agree_prefix`, `above_iterations`, and `not_occurs_prefix`).
- Lemmas written for a program (the summaries of inner loops, the inductions,
  the chains of [examples/dafny/algorithms](../examples/dafny/algorithms),
  [algorithms.md](algorithms.md)) follow patterns that the matcher
  imposes:
  - **Variables named apart.** The variables of a lemma are named apart from
    those of the goal, i.e. of the method and its context: a variable of a
    rule with the name of a variable of the goal captures it, e.g. a lemma
    variable `n` that occurs only in its condition is then taken as the
    goal's `n` and the match leaves it unbound ("variables of a rule not
    instantiated"). The binary search of
    [examples/dafny/algorithms/bsearch.dfy](../examples/dafny/algorithms/bsearch.dfy) writes its lemmas
    over `ar`, `len`, `y` for the method's `a`, `n`, `x`.
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
    (`Context.active`, [prove.md](prove.md)). The summaries took
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

### Rewrite rules or forward lemmas

A rewrite rule (`{:rw}`) applies where its left-hand side occurs; a forward lemma (`{:fw}`) is assumed by `-prove`
wherever a term matching its trigger occurs in an assumed fact (see [prove.md](prove.md)). The choice per kind of
lemma:

- **Rewrite rules**: trace introductions and folds, which name a trace (`trace(...) == stores(...)`, `bisection`);
  equations that compute a value (`current(counter(i, c, n)) == ...`, `earlier(j, ⌊sums(...)⌋) == ...`); atoms that
  occur in goals as they are, e.g. postconditions (`sorted_short`, `perm_refl`); the rules on `invs` atoms of
  iteration constraints.
- **Forward lemmas**: facts about a term whose atom rarely occurs literally, but which the arithmetic or the classes
  need where the term occurs: bounds of a trace or of a named value (`bisection_lo`, `bounds` of the partition
  points, the triangles), bounds and (dis)equations at reads (`earlier_above_iterations`, `earlier_agree_prefix`,
  `select_not_occurs_selects`), facts that refute an atom (`natural_positive`, `store_occurs_selects`).
- **Both**, a rule on the atom and a forward lemma on the term, only where an example shows that the atom must be
  decided where no fact was assumed, e.g. a side condition decided inside an update; otherwise the forward fact
  suffices, since closed conditions are looked up among the facts.

Triggers belong on named terms (a function of the database), not on raw trace patterns: a trace pattern is matched
through the views at every read of every component, in every sibling context; so a forward lemma about a trace comes
with a rule that names the trace (the bisection). The firing at every assumed fact is quadratic in the conjuncts of
a premise; with dozens of forward lemmas, the firing with a memo per lemma and term is needed first
(ideas/prove-next.md). The order of a file matters for rules as well: a rule whose pattern subsumes another must come
after it (`sum_add` after `sum_neg` and `sum_scale`).

## The semantics in Lean ([lean/](../lean))

The lemmas of the stable modules, teq.dfy, `aggregation.dfy`,
`arithmetic.dfy`, `search.dfy`, `sorted.dfy`, `arrays.dfy`, `counters.dfy`,
`strides.dfy` and `unsigned.dfy` (`MODULES` of
[scripts/lean/generate.py](../scripts/lean/generate.py)), are proved in Lean 4
(core, without Mathlib, the toolchain of `lean-toolchain`), in the Lake
project at the root (`lakefile.toml`, sources in `lean/`):

- [Semantics.lean](../lean/TEQ/Semantics.lean), by hand: the datatype
  `Trace`, a value followed by the trace of the remaining iterations (`step`)
  or a last value (`stop`), hence never empty, and the combinators. There is a
  single combinator of each kind, `trace`, `maps`, and `invs`, defined by
  recursion over one dependency, `trace` as a right fold; the Lean printer
  zips several dependencies, `List.zip d₁ (List.zip d₂ d₃)`, binds their
  values by a tuple, `fun acc ⟨b₁, b₂, b₃⟩ => ...`, and prints guarded cases
  as conditionals that end in `unspecified` where no guard holds, as in the
  core, such that complete guards are an obligation of the proofs.
- The functions that the engines use through their lemmas only, `cut`,
  `sorted`, `perm`, `partitioned`, `lower` and `upper`, have definitions in
  the modules without `{:rw}` (no rules), which the proofs use. `bisection`
  is a definition with `{:fold}`, whose folding is the only rule on it; a
  third case keeps the state where `lo < hi` fails or no guard holds, which
  makes it total (see complete guards below).
- [Database.lean](../lean/TEQ/Database.lean), generated: the functions of the
  modules as printed by `-print lean`, and each lemma as a proposition
  `Stmt.<name>` of its printed statement, with the premises of
  [premises.txt](../lean/premises.txt). Sequences are lists, arrays functions,
  `length` is declared in teq.dfy with `{:lean}` as `List.length` of Lean.
- [Proofs.lean](../lean/TEQ/Proofs.lean), by hand: a theorem of the name of
  each lemma with its statement (`<name>_rule` for a lemma named like a
  function, `lower` and `upper` of sorted.dfy, also for its `Stmt`, since the
  body of `Stmt.lower` would resolve `lower` to it), and the auxiliary lemmas
  (the theorems of the lemmas that the stable modules no longer contain were
  removed with the legacy database on Oct 23, 2026).
- [Check.lean](../lean/TEQ/Check.lean), generated:
  `example : Stmt.<name> := @<name>` for each lemma, so a lemma whose
  statement changed or that has no proof fails the build.
- [Counterexamples.lean](../lean/TEQ/Counterexamples.lean), by hand: the
  lemmas without their premises are false.
- [open.txt](../lean/open.txt): the lemmas without a proof, which the
  generator removes from the modules before printing, each with the reason;
  empty since the bisection became a total definition (Oct 14, 2026).

The dependencies of a combinator have equal lengths, which `zip` in Lean does
not assume: `-print lean` adds hypotheses on the lengths to each lemma
(`lean.Printer.lengths`), `(hxs : length xs = n)` for each list variable that
is a dependency of a combinator, also through a `{:fold}` function, or that is
read at the iterations `k` of a counter by `earlier(natural(k), xs)`, where `n`
is the number of steps of a counter among the dependencies or a further
parameter `(n : Nat)` of the lemma. The premises that the printer cannot see
and that the engine does not check are listed in `premises.txt`, each with the
reason why the contexts of `-teq` provide it: reads within the loop
(`integer k < integer n` of `earlier_counter`, `earlier_sums`, ...), prefixes
not longer than the list (`prefix_counter`), the lengths of lists that are
no dependency of a combinator (`earlier_not_occurs_prefix`).

Complete guards need no premise. A lemma with arbitrary guards (`bisection`,
`current_trace_bounded`, `current_trace_increasing`) ends in a case for the
complement of the others, whose result keeps the conclusion true, so the
lemma holds for every update. The traces of the loops have no such case and
still match: the matcher requires each case of the expression to be covered
by a case of the pattern, not the converse, and the guards of the traces of
`-teq` are complete in the contexts of their updates by construction (the
iteration constraints), which the rules maintain.

- Check with `scripts/lean/check.sh` (about 20 s from scratch): it fails if
  the generated files are not those of the current modules, if the build
  fails, or on a `sorry`; `--regenerate` regenerates them first.
- A new or changed lemma of a stable module: edit the module, run
  `scripts/lean/generate.py` (it prints the modules with a copy of
  `cuvee.jar`, hence after the assembly if the printer changed), prove
  `Stmt.<name>` by a theorem `<name>` in Proofs.lean at the position of its
  group, and add a premise to `premises.txt` only if the lemma is false
  without it, with a counterexample in Counterexamples.lean. A definition that
  does not check is fixed in the module or in `lean.Printer`, never in the
  generated file.
- A module that becomes stable joins `MODULES`; until then, the proofs of its
  lemmas of the former single file stay in Proofs.lean unchecked against its
  statements. The lemmas of `nested` have no proofs; a lemma that cannot be
  proved yet goes to `open.txt` with the reason.

## The fallback encoding `-fallback` ([Fallback.scala](../src/cuvee/transform/Fallback.scala))

After section 5.3 of the paper, `-fallback` lowers the goals into first-order
logic for solvers, e.g. `-teq -prove -split -prove -fallback -z3`;
nothing polymorphic remains of the lemma database, hence no `-monomorph`.

- The variables of traces and lists bound by universal quantifiers of
  positive polarity, e.g. of `∀ xs. φ ⇒ ψ`, or by existential ones of
  negative polarity become uninterpreted functions of an integer index,
  with a fresh index, since the goals of `-split` share variables; those of
  other quantifiers are errors.
  A trace `X` of `n` steps has the entries `X(0), ..., X(n)`, `current(X)`
  is `X(n)`, `⌊X⌋` the same function below `n`; `earlier(k, ⌊X⌋)` is
  `X(k)`. Naturals become integers, `natural(x)` is `x` if nonnegative and
  0 otherwise; equations and conditionals of naturals are rebuilt over the
  integers, e.g. the number of iterations `n == natural(i)` of a loop is
  `n == (if 0 <= i then i else 0)` (before 0.46.7 they were generalized like
  the other functions of naturals, which lost the relation of `n` and `i`).
  These functions, `=` and `ite`, are an explicit list (`Fallback.lowered`),
  since nothing marks the functions of the prelude; an application of one of
  them over naturals without traces or lists that reaches the generalization
  is an error ("function over naturals not lowered by -fallback") instead of
  a silently weaker goal.
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
- Applications of functions defined with `{:fold}` whose result is no trace
  or list, e.g. `squares(i, n)` of `teq:series`, are unfolded as well, and
  their bodies lowered (since 0.50.15; before, they were generalized like the
  other functions of trace equation systems, which lost the sums that z3
  evaluates for bounded inputs, e.g. of `cohencu-ll_valuebound1`).
- A trace `S` of several accumulators is one function per accumulator,
  `S_0(j)`, `S_1(j)`, ... (`Fallback.head`; the lowered head is a tuple of
  their applications, which no output contains): the equation
  `S == trace(e₀, e₁, ...)` states `S_i(0) == eᵢ` and the cases of the result
  `uᵢ` for `S_i(j + 1)`, in which the accumulators are `S_0(j)`, `S_1(j)`,
  ...; `current(S).i` is `S_i(n)` and `⌊S⌋.i` the same function below `n`.
  Lists of such traces have one length function for all components.
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
- Lemmas that are not free are lowered like goals: checking the stronger
  lowered lemma is sound, and the solver assumes it only once it holds, for
  all interpretations of the fresh functions; a refutation is `unknown`
  (`:abstract`). Polymorphic goals and lemmas are errors. The declarations of
  the lemma database and the axioms and free lemmas over traces, lists, and
  naturals are dropped, which is sound for assumptions, unlike assuming
  their stronger lowering.
- Tests: [fallback.dfy](../examples/dafny/teq/fallback.dfy),
  [fallback_count.dfy](../examples/dafny/teq/fallback_count.dfy),
  [fallback_negated.c](../examples/c/teq/fallback_negated.c),
  [fallback_nested.c](../examples/c/teq/fallback_nested.c),
  [fallback_recursion.dfy](../examples/dafny/teq/fallback_recursion.dfy),
  [fallback_accumulators.dfy](../examples/dafny/teq/fallback_accumulators.dfy),
  [fallback_lemma.dfy](../examples/dafny/teq/fallback_lemma.dfy),
  [invalid_fallback_polymorphic.dfy](../examples/dafny/teq/invalid_fallback_polymorphic.dfy)
  (a cycle).

## Simplification and rewriting

- The simplifier's helpers `trace`, `maps`, and `invs`
  ([Simplify.scala](../src/cuvee/prove/Simplify.scala)) collapse equal
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
- The rewrite engine ([Rewrite.scala](../src/cuvee/prove/Rewrite.scala))
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
- [RewriteTraces.scala](../test/src/cuvee/test/prove/RewriteTraces.scala)
  tests the rewrite engine with the examples of the paper (counters,
  summations, `selects`) in single steps; `examples/dafny/prove/traces*.dfy`,
  `dependencies.dfy`, and `invariants.dfy` the simplifier and the rewrite rules on
  traces, which declare `Trace` and the functions on traces as in teq.dfy.
- E.g. `./Cuvee.sh -teq -prove examples/dafny/vcgen/sum.dfy`.
