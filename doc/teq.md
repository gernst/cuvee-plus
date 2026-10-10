# Trace equation systems

Verification by symbolic execution and trace equation systems (TEQs), after
*Trace Equation Systems for Program Verification*. Loops are summarized by
equations over traces, which the simplifier rewrites with a lemma database
until the goal is proved. SMT solvers are not expected to solve TEQs: there
are no special cases for traces in the solver interface, no implicit
monomorphization, and no implicit introduction of TEQ concepts to the solvers.

## Combinators ([Expr.scala](../src/cuvee/core/Expr.scala))

```scala
case class Upd(cond: Expr, rhs: Expr)                         // if cond then rhs
case class Eps(updates: List[Upd])                            // some rhs whose cond holds
case class Trace(init: Expr, deps: List[Expr], acc: Var, bound: List[Var], update: Expr)
case class Maps(deps: List[Expr], bound: List[Var], update: Expr)
case class Invs(deps: List[Expr], bound: List[Var], body: Expr)
```

After section 3 of the paper:

- `Trace(init, deps, acc, bound, update)` is the trace of the accumulator
  `acc`, of type `Trace(T)`. It starts with `init`; each further value is the
  update of the previous one and the next values of the dependencies, which
  `bound` ranges over point-wise.
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
  `teq.dfy` (`Unspecified`). `List[Upd]` has `free`, `params`, and
  `map` like lists of expressions.
- The functions on traces are in `Fun.trace`: `counter`, `current`, `butlast`
  (the paper's `⌊X⌋`), `length`, `earlier`; `Counter`, `Current`,
  `Butlast`, `Earlier`, and `Length` in
  [Builtin.scala](../src/cuvee/core/Builtin.scala) are their sugar. The sort is `Sort.trace(elem)`.
- `state.exprs.trace`, `map`, and `all` create the bound variables with the
  element types of the dependencies (`Type.elem`).

## Syntax

| Combinator | Dafny and Boogie | SMT-LIB |
|---|---|---|
| `Trace` | `trace(e, for Y, Z do x, y, z :: u)` | `(trace (x e) ((y Y) (z Z)) u)` |
| `Maps` | `maps(for Y yield y :: u)` (Boogie: `map(...)`) | `(map ((y Y)) u)` |
| `Invs` | `invs(for Y check y :: φ)` (Boogie: `all(...)`) | `(invs ((y Y)) φ)` |
| update | `case φ₁ => e₁ case φ₂ => e₂` | `(eps (φ₁ e₁) (φ₂ e₂))` |

`⌊X⌋` is `butlast(X)` in Dafny and Boogie.

## The transform `-teq` ([TEQ.scala](../src/cuvee/verify/TEQ.scala))

`TEQ` replaces each procedure definition by a goal from symbolic execution,
after section 4 of the paper.

- A `Path` holds the fresh variables for nondeterministic choices, the values
  of the variables as a substitution, and the assumptions, branch conditions,
  and checks along the way. Choices `if *` become branches on fresh booleans,
  calls are inlined, which requires procedures without a contract (e.g. C
  functions) and does not terminate for recursive ones.
- Each loop yields a single path (theorem 4.8), which assumes its trace
  equation system (definition 4.4): one `Trace` per modified variable, whose
  update has a case per path through the body, the counter
  `K = counter(0, 1, n)`, and the iteration constraint `Invs`, and which
  checks that the body executes safely from the current state.
- A loop whose body ends by `break` or `return` on all paths runs it at most
  once: its body is a conditional on the test, without a trace equation
  system, where `break` continues after the loop.
- The goal is that all checks hold and the postcondition follows on every
  path.
- Differential equations and parallel composition are not supported; loop
  invariants are ignored.

## The lemma database ([teq.dfy](../resources/cuvee/teq.dfy))

- Injected by the source with `-teq`, after its prelude (`Config.features`):
  Dafny input parses it with its own parser, such that the input can refer to
  its declarations, other input with a fresh Dafny parser; the TEQ transform
  relies on it. It defines the datatype `Trace`, declares the functions on traces,
  and lemmas about them, which are `{:rw}` (rewrite rules of `-simplify`) and
  free, without a body (assumed by the solvers without proof). Lemmas that
  identify a trace with a function of teq.dfy are named after it, e.g.
  `stores_def` (likewise `selects_def` for `maps`, `agree_prefix_def` for
  `invs`), those about an accessor of such a function after both, e.g.
  `current_sums` or `earlier_prefix`, the others after what they state,
  e.g. `current_trace_two_phases` or `sum_add`.
- `Trace` exists only with `-teq`. Inputs that use traces without `-teq`
  declare `Trace` themselves; Dafny inputs with `-teq` use the declarations of
  the database, inputs in other languages cannot.
- All function declarations come first, then the lemmas, grouped by the
  function of their left-hand side (the combinator, `current`, `prefix`, ...).
  Rules are tried in the order of the file, lemmas whose order matters keep it
  within their group.
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
- Auxiliary predicates abstract iteration constraints, e.g. `agree_prefix`,
  and are only declared; their names avoid those that inputs declare with
  other meanings, since equal signatures are identified.

## The semantics in Lean ([teq.lean](../resources/cuvee/teq.lean))

- `Trace` is a datatype of teq.dfy, a value followed by the trace of the
  remaining iterations (`step`) or a last value (`stop`), hence never empty,
  with `current` and `butlast` defined by recursion; teq.lean takes them
  from the printed teq.dfy. The functions that teq.dfy only declares are
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
- The functions that teq.dfy defines with `{:fold}` and the lemmas are
  printed by `-print lean`, the lemmas as theorems, all `sorry` for now.
- Checked counterexamples show lemmas that hold only under assumptions that
  the contexts of the goals provide, e.g. `n ≥ 0` or dependencies of equal
  length.
- Check with `lean resources/cuvee/teq.lean` (Lean 4.34); teq.lean is built
  from the output of `./Cuvee.sh -print lean resources/cuvee/teq.dfy` and
  the hand-written definitions at its beginning.
- The dependencies of a combinator have equal lengths, which `zip` in Lean
  does not assume: `-print lean` adds hypotheses on the lengths to each
  lemma (`lean.Printer.lengths`), `(hxs : length xs = n)` for each list
  variable that is a dependency of a combinator, also through a `{:fold}`
  function, or that is read at the iterations `k` of a counter by
  `earlier(natural(k), xs)`, where `n` is the number of steps of a counter
  among the dependencies or a further parameter `(n : Nat)` of the lemma;
  `length` is declared in teq.dfy with `{:lean}` as `List.length` of Lean.
  With them, all lemmas of teq.lean are proved; assumptions on indices
  within the lists are added by hand there as `requires` to be added to
  teq.dfy.

## The fallback encoding `-fallback` ([Fallback.scala](../src/cuvee/transform/Fallback.scala))

After section 5.3 of the paper, `-fallback` lowers the goals into first-order
logic for solvers, e.g. `-teq -simplify -split -simplify -fallback -z3`;
nothing polymorphic remains of `teq.dfy`, hence no `-monomorph`.

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
  fresh length function, and the other functions of `teq.dfy` (`sum`,
  `occurs`, ...) are replaced by fresh functions without definition, which
  generalizes the goal: a model of the solver need not be a counterexample.
- The declarations and lemmas of `teq.dfy` and lemmas over traces, lists,
  and naturals are dropped.
- Tests: [fallback.dfy](../examples/dafny/teq/fallback.dfy),
  [fallback_count.dfy](../examples/dafny/teq/fallback_count.dfy),
  [fallback.c](../examples/c/teq/fallback.c),
  [fallback_negated.c](../examples/c/teq/fallback_negated.c),
  [fallback_nested.c](../examples/c/teq/fallback_nested.c).

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
  line, e.g. `-teq -split -simplify`, and the goals that remain in their
  expected output (none if they are proved).
- [TEQ.scala](../test/src/cuvee/test/dafny/TEQ.scala) checks the goals of
  `-teq`, the injection of the database, and the lemmas on core terms
  (`Rules.from(State.empty, TEQ.lemmas)` with `Rewrite`).
- [RewriteTraces.scala](../test/src/cuvee/test/simplify/RewriteTraces.scala)
  tests the rewrite engine with the examples of the paper (counters,
  summations, `selects`) in single steps; `examples/dafny/simplify/traces*.dfy`,
  `dependencies.dfy`, and `invariants.dfy` the simplifier and the rewrite rules on
  traces, which declare `Trace` and the functions on traces as in `teq.dfy`.
- E.g. `mill -i run -teq -simplify examples/dafny/vcgen/sum.dfy`.
