# Trace equation systems

Verification by symbolic execution and trace equation systems (TEQs), after *Trace Equation Systems for Program
Verification*. Loops are summarized by equations over traces, which `-prove` rewrites with a lemma database until the
goal is proved ([prove.md](prove.md)). SMT solvers are not expected to solve TEQs: there are no special cases for
traces in the solver interface, no implicit monomorphization, and no implicit introduction of TEQ concepts to the
solvers; `-fallback` lowers what remains into first-order logic.

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

- `Trace(inits, deps, accs, bound, results)` is the trace of the accumulators `accs`, of type `Trace(T)` for one and
  `Trace((T₁, ..., Tₘ))` for several, where the tuple type names the state and no term of tuple type is built. It
  starts with `inits`; each further value is the results for the previous values and the next values of the
  dependencies, which `bound` ranges over. `Trace(init, deps, acc, bound, update)` builds the single case,
  `Trace.single` matches it.
- `Component(S, i)` is component `i` of the last value of a trace of several accumulators, `History(S, i)` the list
  of its earlier values, of type `List(Tᵢ)`; histories are dependencies like any other. Components are read only by
  these two, never by tuple selectors.
- `Maps(deps, bound, update)` is the sequence of the updates, `Invs(deps, bound, φ)` states `φ` for all values of the
  dependencies.
- Dependencies are sequences, at least one, all of equal length (`Type.dependencies`), e.g. `⌊K⌋` of a trace `K`. A
  trace of `n` steps has `n + 1` values: those of `⌊X⌋` (`earlier(0..n-1, ⌊X⌋)`) and `current(X)`. Goals contain no
  lengths: the number of iterations is the `n` of the counter `K == counter(0, 1, n)`, an integer with `0 <= n`.
- An update is a single result or guarded cases `Eps(List(Upd(φᵢ, eᵢ), ...))` with disjoint guards. Guards need not
  be complete (`break`); an update where no guard holds is `unspecified`. The simplifier flattens nested `Eps`, merges
  cases with equal results, and replaces a single case by its result. Conditionals in the results of a trace that are
  not below a binder are lifted into cases (`Simplify.cases`), e.g. `ret < a[i] ? a[i] : ret` of C into
  `case ret < v => v case v <= ret => ret`, the form of branching statements, which the patterns of the lemmas name
  (examples/c/teq/ite_cases.c).
- The functions on traces are in `Fun.trace` (`counter`, `current`, `butlast` for `⌊X⌋`, `length`, `earlier`), with
  the sugar `Counter`, `Current`, `Butlast`, `Earlier`, `Length` ([Builtin.scala](../src/cuvee/core/Builtin.scala)).

## Syntax

| Combinator | Dafny and Boogie | SMT-LIB |
|---|---|---|
| `Trace` | `trace(e, for Y, Z do x, y, z :: u)` | `(trace (x e) ((y Y) (z Z)) u)` |
| `Trace`, several accumulators | `trace(e₁, e₂, for Y do x₁, x₂, y :: u₁, u₂)` | `(trace ((x₁ e₁) (x₂ e₂)) ((y Y)) u₁ u₂)` |
| `Component`, `History` | `current(S).1`, `⌊S⌋.1` | `((_ current 1) S)`, `((_ butlast 1) S)` |
| `Maps` | `maps(for Y yield y :: u)` (Boogie: `map(...)`) | `(map ((y Y)) u)` |
| `Invs` | `invs(for Y check y :: φ)` (Boogie: `all(...)`) | `(invs ((y Y)) φ)` |
| update | `case φ₁ => e₁ case φ₂ => e₂` | `(eps (φ₁ e₁) (φ₂ e₂))` |

`⌊X⌋` is `butlast(X)` in Dafny and Boogie. In Lean, a trace of several accumulators is a trace of their product,
its components are selected from nested pairs, `(current S).2.1`, and its histories are `maps (butlast S) (...)`.

## The transform `-teq` ([TEQ.scala](../src/cuvee/verify/TEQ.scala))

`TEQ` replaces the entry point (`-entry`, or `main` in C) by a goal from symbolic execution, after section 4 of the
paper; calls of procedures without a contract are inlined, so they are checked in the context of their calls.

- A `Path` holds the fresh variables of nondeterministic choices, the values of the variables, and the assumptions,
  branch conditions and checks along the way. Calls with a contract are by the contract, as in `-vcgen`.
- Each loop yields one path that assumes its system: one `Trace` per strongly connected component of the modified
  variables (below), the counter `K == counter(0, 1, n)` with `0 <= n`, and the iteration constraint `Invs`; it checks
  that the body executes safely from the current state. Its exits (the negated test, `break` or `return` in a last
  iteration) are told apart by branch conditions, which an enclosing loop uses as the guards of its cases.
- The update of a variable has one case per path through the body; cases with the same result are grouped, their
  guards joined by a disjunction (`TEQ.update`), e.g. the paths of a body that does not modify the variable
  ([stores_cases_point.c](../examples/c/teq/stores_cases_point.c)).
- A loop whose body ends by `break` or `return` on all paths runs at most once and is a conditional.
- `TEQ.loop` is `TEQ.head`, the system from the state at the entry, followed by `TEQ.exits`; `-slice` uses
  `TEQ.head` at the heads of loops ([prove.md](prove.md), "Programs").
- The goal is that all checks hold and the postcondition follows on every path. Differential equations and parallel
  composition are not supported; loop invariants are ignored.

### The partition into components

The modified variables of a loop are partitioned by the strongly connected components of their read relation
(`TEQ.system`, `util.SCC`): a variable reads the variables of its results and, if the paths are guarded, of the
guards. Each component, after those it reads, becomes one trace: a single accumulator for a variable in no cycle, as
in the paper, several for a cycle, with the counter, the histories of the components it reads and the choices as
dependencies. The choices of a loop are lists `Z?` with one value per iteration, stated as `length(Z?) == n` for the
number of iterations `n`, since they are the only dependencies that are no traces over the counter; the length lemmas
of teq.dfy (`length_counter`, `length_prefix`, `length_eq_zero`, ...) reduce these facts where the lists are known, so
that a choice still occurs only in its equation for the one-point rule. (An experiment with the choices as arrays read
over the counter, `selects(Z?, ⌊K⌋)`, is on the branch `choices-arrays`: the arrays carry values beyond the iterations,
so the facts about the choices became equations of `selects` terms that the variable cannot carry.) The exit values are `current(X)` and `current(S).i`. The component graph is acyclic, so the system of a
nested loop is closed: its counter, traces and exit values are substituted by their definitions, and an inner loop is
a value of the outer update; an outermost loop keeps its definitions as equations, which the engine follows through
the classes. The per-variable traces of a cycle are views ([prove.md](prove.md)), and a rule may also match a cycle as
a whole, e.g. the bisection of binary search.

## The lemma database ([resources/cuvee/teq](../resources/cuvee/teq))

[teq.dfy](../resources/cuvee/teq.dfy) is the entry point, which `-teq` injects after the prelude (`TEQ.modules`,
`Config.features`): the types `List` and `Trace`, the functions on traces and the lists they need, and the lemmas
about traces. Dafny input parses it with its own parser, so the input can refer to its declarations. The optional
modules are injected after it by `-include teq:<concept>`:

| Module | Contents |
|---|---|
| `aggregation` | `sum`, `count`, `max`, `min`, `parity` and the traces `sums`, `parities`, `counts`, `maxs`, `mins`; compactions and filters (`compacts`, `filters_above`, `filters_below`) |
| `arithmetic` | `pow`, and the facts the arithmetic does not decide alone, e.g. halved triangles |
| `search` | agreeing prefixes, no occurrence, values above the iterations, the bisection with a probe |
| `sorted` | `sorted`, `perm`, `partitioned`, `swap`, the partition points `lower`, `upper` |
| `arrays` | stores at a counter and at distinct keys, conditional stores, resets, reads along a trace, rows of two-dimensional arrays, copies from both ends |
| `counters` | phases, flags, catching up, merged cases, constant, increasing and bounded values |
| `strides` | strided stores and stores ahead (MonoCera) |
| `unsigned` | `mods(i, c, m, n)`, the counter modulo `m` of unsigned C variables |
| `series` | the folds `squares`, `cubes`, `fourths`, `fifths`, geometric `series`; after `aggregation`, `arithmetic` |
| `multisets` | the multiset of a list (`elems`, the multisets of the core) and the folds that do not depend on the order as folds of it (`msum`, `mparity`, `mmax`, `mmin`, the multiplicities); the sums and parities of reads at keys converted to them; swap, shift and rotation of arrays preserve the multiset; after `aggregation`, not in `-svcomp`; each lemma of `aggregation` that consumes a fold of a list has its twin on the fold of the multiset here (ideas/multisets.md) |

Rules are tried in the order of the modules and of the files, so the order decides which abstraction a fragment
gets; a rule whose pattern subsumes another comes after it. Within a module, the function declarations come first,
then the lemmas grouped by the function of their left-hand side.

**Counts are integers.** Counts, lengths and positions (`n` of `counter`, `consts`, `prefix` and the folds, `k` of
`earlier(k, xs)`, `length(xs)`) are `int`. The definitions clamp: `counter(i, c, n)` is `stop(i)` for `n <= 0`,
`prefix(k, xs)` is `nil` for `k <= 0`, `earlier(k, xs)` is `unspecified` for `k < 0`. A lemma has `requires 0 <= n`
where it needs it, e.g. `current(counter(i, c, n)) == i + n * c`; `-teq` states `0 <= n` for every loop, so the simplex
decides these conditions. Lemmas that hold for all integers by the clamping have no condition.

**Kinds of declarations.**
- Lemmas are `{:rw}` (rewrite rules) or `{:fw}` (forward lemmas) and free, assumed by solvers without proof.
- Definitions by a `match` that recur structurally are `{:rw}`, one rule per case (`current`, `butlast`, `earlier`,
  `prefix`, `occurs`, `indexof`, `distincts`, `sum`, `parity`, `count`); they apply only to constructors, so traces
  of programs are not unfolded. Definitions by a test on an integer (`counter`, `consts`, `cutFrom`) are not rules,
  their rule would unfold without end.
- A function that is a trace or a map is a fold (`{:fold}`): its definition is a rule that folds the trace into the
  function (`stores`, `sums`, `selects`, `mods`, ...), standing among the lemmas at the position of its rule. A fold
  need not be a trace: `swap(a, p, q)` folds `a[p := a[q]][q := a[p]]`. A lemma `<name>_def` remains where a function
  cannot be its own fold (`counter_def`, `consts_def`).
- Iteration constraints are abstracted by folds of their constraints (`above_iterations`) or rewritten into atoms
  (`not_occurs_prefix`, `invs_agree_prefix`: the equation of prefixes); an iteration constraint is never a side
  condition, since deciding it builds the contexts of the `invs` facts, whose reads would match the rule again. The
  facts at the reads are rules on the comparisons of the reads with the abstractions as side conditions
  (`earlier_eq_prefix`, `earlier_above_iterations`, `select_eq_not_occurs_selects`).
- Names: lemmas about an accessor of a function after both (`current_sums`, `earlier_prefix`), others after what they
  state (`counts_true`, `sum_add`); trace-producing functions plural (`sums`), their scalar counterparts singular.
  A lemma that at most three proved SV-COMP tasks use says so in its `(from ...)` line (`scripts/rules.py`).
- `Trace` exists only with `-teq`; inputs that use traces without it declare `Trace` themselves.

**Rewrite rules or forward lemmas.**
- Rewrite rules: trace introductions and folds that name a trace, equations that compute a value
  (`current(counter(i, c, n))`, `current_trace_step_or_keep`), atoms that occur in goals as they are
  (`sorted_short`), the rules on `invs`, and facts at reads as rules on the comparison of the read
  (`earlier_eq_prefix`), whose other variables are bound by the side conditions; a rule is tried only at its atom,
  a forward lemma at every term of every assumed fact.
- Forward lemmas: facts about a term whose atom rarely occurs, but which the arithmetic or the classes need where the
  term occurs: bounds of traces or named values (`bisection_lo`, the triangles).
- Both only where an example needs the atom decided where no fact was assumed.

**What a forward lemma costs.** A trigger is tried at every matching term of every assumed fact, also where it never
yields an instance, so:
- triggers belong on folds (`squares(i, n)`), not on general terms such as any sum over a counter or the current value
  of any trace, and not on raw trace patterns, which are matched at every read of every component;
- one fact per lemma: `-split` splits a lemma at its conjunctions, and each part gets the trigger of its own terms;
- no variables bound by conditions alone: such a variable is matched against every member of a class, one instance
  each; state the fact in the term itself;
- degenerate arguments of folds get a rule that evaluates them (`squares_zero`).
- no facts that no rule normalizes: an instance is simplified again at every firing (a memo of the instances was
  tried and costs more, doc/prove.md), and one that the simplifier
  cannot reduce, e.g. a disjunction with an occurrence in the values of a store, comes back unchanged at every read
  of every store. The removed `store_occurs_selects` (`occurs(x, selects(a[j := x], ⌊counter(0, 1, n)⌋)) || n <= j`,
  triggered at the reads of stores, for standard_sentinel-2) used up the steps of the reducers of array-crafted and
  reducercommutativity this way; a fact that refutes an atom belongs in a rewrite rule on that atom, here
  `invs_select_store_ne` on the iteration constraint of the search.

**Lemmas written for a program** (summaries of inner loops, the chains of
[examples/dafny/algorithms](../examples/dafny/algorithms), [algorithms.md](algorithms.md)) follow the matcher:
- their variables are named apart from those of the goal and of the database rules (`x`, `n`, `Ks`, ...), or a rule
  variable captures them;
- a left-hand side `invs(...)` with a bare bound variable on one side of its body (`n <= j`) matches every comparison
  fragment; a function symbol on that side makes it specific;
- a condition may mention the rule's own left-hand side, since the rule is suspended while its conditions are
  evaluated;
- the exit of an outer loop is a disjunction in the conclusion; a postcondition stated as two implications gives each
  goal its literal;
- a file includes only the modules its lemmas are written for, since summaries match the fragment forms they produce.

Diagnostics: truncated copies of a summary with its first k conditions find the first failing one; every result is
checked on a program with a wrong postcondition, which must leave a goal.

## The semantics in Lean ([lean/](../lean))

The lemmas of teq.dfy and the stable modules (`MODULES` of [generate.py](../scripts/lean/generate.py)) are proved in
Lean 4 without Mathlib, in the Lake project at the root ([lean/README.md](../lean/README.md)):

- [Semantics.lean](../lean/TEQ/Semantics.lean): the datatype `Trace` (`step`, `stop`, never empty) and the
  combinators `trace`, `maps`, `invs` over one dependency; the printer zips several and prints guarded cases as
  conditionals that end in `unspecified`.
- [Database.lean](../lean/TEQ/Database.lean) (generated): the functions as printed by `-print lean`, and each lemma
  as a proposition `Stmt.<name>` with the premises of [premises.txt](../lean/premises.txt).
- [Naturals.lean](../lean/TEQ/Naturals.lean): the definitions over naturals (namespace `TEQ.N`) and the proofs by
  induction on them; [Proofs.lean](../lean/TEQ/Proofs.lean): one bridge per definition, the integer definition being
  the natural one at `toNat` (`counter i c n = N.counter i c n.toNat`), and the theorem of each lemma from that of
  `N`.
- [Check.lean](../lean/TEQ/Check.lean) (generated): `example : Stmt.<name> := @<name>` for each lemma.
- [Counterexamples.lean](../lean/TEQ/Counterexamples.lean): the lemmas without their premises or conditions are false.
- [open.txt](../lean/open.txt): lemmas without proof, removed from the modules before printing (empty).

The dependencies of a combinator have equal lengths, which `zip` does not assume: `-print lean` adds hypotheses
(`lean.Printer.lengths`), `length xs = n` for each list that is a dependency of a combinator (also through a fold),
where `n` is the steps of a counter among the dependencies or a parameter of the lemma, and `n ≤ length xs` for a list
that is only read at the iterations of a counter. Premises that the printer cannot see and the engine does not check
are in `premises.txt`, each with the reason why the contexts of `-teq` provide it (reads at `0 ≤ k < n`, prefixes not
longer than the list). Complete guards need no premise: a lemma with arbitrary guards ends in a case for the
complement, and the matcher requires each case of the expression to be covered by the pattern, not the converse.

- Check with `scripts/lean/check.sh` (fails on stale generated files, a failed build, or a `sorry`; `--regenerate`
  first regenerates).
- A new or changed lemma: edit the module, run `scripts/lean/generate.py` (after the assembly if the printer
  changed), prove `Stmt.<name>` in Proofs.lean, and add a premise only if the lemma is false without it, with a
  counterexample. Definitions are fixed in the module or in `lean.Printer`, never in generated files.

## The fallback encoding `-fallback` ([Fallback.scala](../src/cuvee/transform/Fallback.scala))

After section 5.3 of the paper, `-fallback` lowers the remaining goals into first-order logic for solvers, e.g.
`-teq -prove -split -prove -fallback -z3`; nothing polymorphic remains, hence no `-monomorph`.

- Variables of traces and lists bound by universal quantifiers of positive polarity (or existential ones of negative
  polarity) become uninterpreted functions of an integer index; others are errors. A trace `X` of `n` steps has the
  entries `X(0), ..., X(n)`, `current(X)` is `X(n)`, `⌊X⌋` the same function below `n`, `earlier(k, ⌊X⌋)` is `X(k)`.
- The length of all dependencies of a combinator is the `n` of its first one, `⌊counter(0, 1, n)⌋`, written directly
  or by an equation among the hypotheses of the quantifier (`Fallback.hypotheses`); lists whose length follows from
  no hypothesis get a fresh length. Counters are inlined, their entries are `i + j * c`.
- A list of traces is a function of two indices, `K(j, i)`, with a length function `K_length(j)`.
- `X == trace(...)`, `maps(...)` and applications of folds become their characterizations,
  `X(0) == e && ∀ j. 0 <= j < n ==> (φᵢ ==> X(j + 1) == eᵢ)`, one implication per case; `invs` is
  `∀ j. 0 <= j < n ==> φ`. A trace of several accumulators is one function per accumulator, `S_0(j)`, `S_1(j)`, ....
- Other combinators are fresh functions of their free variables, defined in the antecedent; equal terms share their
  function if their traces and lists are lowered alike (`Fallback.key`).
- Recursive definitions of the database, by a `match` on a list or by a test `n <= 0` on an integer, whose other case
  recurs on the tail or on `n - 1` (also written `n + -1`) only, are unfolded once per position (`Fallback.recursion`): over a list of length
  `n`, `f_from(n) == base` and `f_from(j) == step(xs(j), f_from(j + 1))`, and `f(xs)` is `f_from(0)`; over an integer
  `n`, `f_upto(j) == base` for `j <= 0` and `f_upto(k + 1) == step(k, f_upto(k))`, and `f(n)` is `f_upto(n)`. A
  definition whose step calls the function otherwise is generalized.
- Other functions of the database and those of the input without a definition become fresh functions, which
  generalizes the goal: a model need not be a counterexample.
- Lemmas that are not free are lowered like goals; a refutation is `unknown` (`:abstract`). The declarations of the
  database and the free lemmas and axioms over traces and lists are dropped. Polymorphic goals are errors.

Tests: `examples/dafny/teq/fallback*.dfy`, `examples/c/teq/fallback*.c`,
[invalid_fallback_polymorphic.dfy](../examples/dafny/teq/invalid_fallback_polymorphic.dfy).

## Simplification and rewriting of combinators

- The helpers `trace`, `maps`, `invs` ([Simplify.scala](../src/cuvee/prove/Simplify.scala)) collapse equal
  dependencies, renaming their bound variables, and drop dependencies whose bound variables are unused, except
  counters; the first one is kept if none remains. `invs` with a constant body is `true` or `len(dep) == 0`, and
  distributes over conjunctions. Results of `Eps` are simplified under their guard and the negations of the others.
- Updates and bodies assume the invariants among the facts whose dependencies are among their own
  (`Simplify.invariants`). If the first dependency counts the iterations, `⌊counter(0, 1, n)⌋` bound to `k`, they also
  assume `0 <= k < n` and `z == earlier(k, ⌊Z⌋)` for each other dependency `⌊Z⌋` bound to `z`
  (`Simplify.iterations`).
- The matcher ([Rewrite.scala](../src/cuvee/prove/Rewrite.scala)) selects the dependencies of the pattern among those
  of the expression, instantiates dependencies that are rule variables by `Maps`, and requires each case of the
  expression to be covered by a case of the pattern, whose guard matches or follows from the guard of the expression.
  Variables left unbound occur only in cases of the pattern that cover no case of the expression and become
  `unspecified`; others are an error of the rule.

## Tests

- `examples/c/teq`, `examples/dafny/teq`: command lines and the goals that remain (none if proved);
  `examples/dafny/vcgen/*.dfy` without loops must generate their goals with `-teq`.
- [TEQ.scala](../test/src/cuvee/test/dafny/TEQ.scala): the goals of `-teq`, the injection of the database, the lemmas
  on core terms (`Rules.from(State.empty, TEQ.lemmas)` with `Rewrite`).
- [RewriteTraces.scala](../test/src/cuvee/test/prove/RewriteTraces.scala) and `examples/dafny/prove/traces*.dfy`: the
  rewriting of combinators, with the declarations of teq.dfy duplicated instead of `-teq`.
