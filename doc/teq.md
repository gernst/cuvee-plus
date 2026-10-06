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
case class Trace(init: Expr, deps: List[Expr], acc: Var, bound: List[Var], updates: List[Upd])
case class Maps(deps: List[Expr], bound: List[Var], updates: List[Upd])
case class Invs(deps: List[Expr], bound: List[Var], body: Expr)
```

After section 3 of the paper:

- `Trace(init, deps, acc, bound, updates)` is the trace of the accumulator
  `acc`, of type `Trace(T)`. It starts with `init`; each further value is the
  update of the previous one and the next values of the dependencies, which
  `bound` ranges over point-wise.
- `Maps(deps, bound, updates)` is the sequence of the updates, of type
  `Seq(T)`.
- `Invs(deps, bound, φ)` states `φ` for all values of the dependencies.
- The dependencies are always sequences (`Seq(T)`), at least one, all of the
  same length (`Type.dependencies`), e.g. `⌊K⌋` of a trace `K`. Their length
  is `Seqs.len` of the theory of sequences (not `Fun.trace.length`). A trace
  with `n` steps has `n + 1` elements: the `n` of `⌊X⌋`
  (`earlier(0..n-1, ⌊X⌋)`) and `current(X)`.
- An update is a list of guarded cases `Upd(φᵢ, eᵢ)` with disjoint and
  complete guards; a single case has the guard `true`. `List[Upd]` has
  `free`, `params`, and `exprs` like lists of expressions.
- The functions on traces are in `Fun.trace`: `counter`, `current`, `butlast`
  (the paper's `⌊X⌋`), `steps`, `length`, `nth`, `earlier`; `Counter` and
  `Butlast` in [Builtin.scala](../src/cuvee/core/Builtin.scala) are their
  sugar. The sort is `Sort.trace(elem)`.
- `state.exprs.trace`, `map`, and `all` create the bound variables with the
  element types of the dependencies (`Type.elem`).

## Syntax

| Combinator | Dafny and Boogie | SMT-LIB |
|---|---|---|
| `Trace` | `trace(e, for Y, Z do x, y, z => u)` | `(trace (x e) ((y Y) (z Z)) u)` |
| `Maps` | `maps(for Y yield y => u)` (Boogie: `map(...)`) | `(map ((y Y)) u)` |
| `Invs` | `invs(for Y check y => φ)` (Boogie: `all(...)`) | `(all ((y Y)) φ)` |
| update | `if φ₁ then e₁, if φ₂ then e₂` | `(cases (φ₁ e₁) (φ₂ e₂))` |

`⌊X⌋` is `butlast(X)` in Dafny and Boogie.

## The transform `-teq` ([TEQ.scala](../src/cuvee/verify/TEQ.scala))

`TEQ` replaces each procedure definition by a goal from symbolic execution,
after section 4 of the paper.

- A `Path` holds the fresh variables for nondeterministic choices, the values
  of the variables as a substitution, and the assumptions, branch conditions,
  and checks along the way. Choices `if *` become branches on fresh booleans,
  calls go by contract.
- Each loop yields a single path (theorem 4.8), which assumes its trace
  equation system (definition 4.4): one `Trace` per modified variable, whose
  update has a case per path through the body, the counter
  `K = counter(0, 1, n)`, and the iteration constraint `Invs`, and which
  checks that the body executes safely from the current state.
- The goal is that all checks hold and the postcondition follows on every
  path.
- Differential equations and parallel composition are not supported; loop
  invariants are ignored.

## The lemma database ([teq.dfy](../resources/cuvee/teq.dfy))

- Parsed by a fresh Dafny parser and injected once at the beginning of the
  output (`TEQ.lemmas`). It declares the type `Trace`, the functions on traces,
  and lemmas about them, which are `{:rw}` (rewrite rules of `-simplify`) and
  `{:free}` (assumed by the solvers without proof).
- `Trace` is in no prelude: it exists only with `-teq`. Inputs that use
  traces without `-teq` declare `Trace` themselves, and inputs cannot use the
  functions of the database, which is injected after parsing.
- All function declarations come first, then the lemmas, grouped by the
  function of their left-hand side (the combinator, `current`, `prefix`, ...).
  Lemmas whose order matters as rewrite rules keep it within their group.
- Functions that produce traces are plural (`sums`, `maxs`, `counts`), their
  scalar counterparts singular (`sum`, `max`, `count`).

## Simplification and rewriting

- The simplifier's helpers `trace`, `maps`, and `invs`
  ([Simplify.scala](../src/cuvee/simplify/Simplify.scala)) collapse equal
  dependencies (by `eq_`), renaming their bound variables to the first one,
  and drop dependencies whose bound variables are unused, except counters
  `⌊counter(...)⌋`; the first one is kept if none remains, since the
  dependencies must be nonempty. `invs` with a constant body is `true` or
  `len(dep) == 0`. Guards and results of updates are simplified, results
  under their guard, and cases with guard `false` are dropped.
- `invs` distributes over conjunctions, `invs(for Y check y => φ && ψ)` is
  `invs(for Y check y => φ) && invs(for Y check y => ψ)`, each with the
  dependencies it uses.
- The updates of `trace` and `maps` and the body of `invs` assume the
  invariants among the assumptions of the context whose dependencies are
  among their own (`Simplify.invariants`), with the bound variables renamed
  to those of the same dependencies. The positions coincide, since the
  dependencies of a combinator have equal length.
- The rewrite engine ([Rewrite.scala](../src/cuvee/simplify/Rewrite.scala))
  matches the binding structure of the combinators: dependencies of the
  pattern are selected among those of the expression (`Binding` relates the
  bound variables), and dependencies that are variables of the rule are
  instantiated by `Maps` expressions. Each case of the expression's update is
  covered by a case of the pattern, whose guard matches syntactically (which
  instantiates bound variables that occur only in guards, e.g. `b` in
  `if b then y + 1`) or follows from the guard of the expression.

## Tests

- `examples/dafny/vcgen/*.dfy` without loops must verify with `-teq -z3`.
- [TEQ.scala](../test/src/cuvee/test/dafny/TEQ.scala) checks the goals of
  `-teq`, the injection of the database, and the lemmas on core terms
  (`Rules.from(TEQ.lemmas)` with `Rewrite`).
- [RewriteTraces.scala](../test/src/cuvee/test/simplify/RewriteTraces.scala)
  tests the rewrite engine with the examples of the paper (counters,
  summations, `selects`); `examples/simplify/traces.smt2` the simplifier.
- E.g. `mill -i run -teq -simplify examples/dafny/vcgen/sum.dfy`.
