# The deduction engine (`-prove`)

The package [prove/](../src/cuvee/prove) is a second engine for the goals of trace equation systems, built
after [ideas/deduction-engine.md](../ideas/deduction-engine.md) and
[ideas/deduction-engine-plan.md](../ideas/deduction-engine-plan.md); the record of its implementation, with the
instructions and the state of each step, is
[ideas/deduction-engine-implementation.md](../ideas/deduction-engine-implementation.md). `-prove` runs it like
`-simplify` runs the simplifier: the assertions and lemmas with `:rw` are its rules, the other assertions are
simplified under a context and dropped when they become `true`. The package is independent of
[simplify/](../src/cuvee/simplify): what it shares with the simplifier (the polynomials, the clauses, the rules, the
traversal and the matcher) is copied and adapted, not referenced, so that the two engines evolve separately.

## What differs from the simplifier

- **Congruence closure** ([`Classes`](../src/cuvee/prove/Classes.scala)) in place of the chains of variable
  equations: a persistent union-find over the terms of the facts, where applications are decomposed into their
  arguments and merged by congruence, and everything else (variables, literals, binders, the combinators) is a node
  of its own. The definitions of a variable are the members of its class that are not variables and do not contain
  it (`Context.defs`), in both orientations and transitively (`K == I` identifies two counters, `x == f(y)` with
  `y == z` gives `f(z)`); the matcher tries them when a pattern does not match the variable itself
  (`Rewrite.matches`). Only variables have definitions: a term matched by a member of its class that contains it, e.g.
  `a[k]` by `S.2[k] == a[k]` assumed from a sibling conjunct, is rewritten to a term that contains it again, without
  end. Two literals or two constructors in one class, or a disequation whose sides are in one class, make the context
  inconsistent. `Simplify.var_` replaces a variable by the literal of its class, or by the canonical variable of the
  class (the smallest by name).
- **A simplex** ([`Simplex`](../src/cuvee/prove/Simplex.scala), [`Linear`](../src/cuvee/prove/Theory.scala)) in
  place of the difference constraints: the general simplex over the rationals with bounds (Dutertre and de Moura),
  strict bounds by an infinitesimal, Bland's rule, built per check from the constraints of the context (memoized per
  context, since `Linear.inconsistent` is lazy). On `Int`, a strict comparison is the non-strict one offset by 1 and the
  coefficients are rounded (`Poly.floor`), so `2 * x < 7` bounds `x` by 3; products of atoms are variables of their
  own. Disequations are refuted when the constraints determine the difference. The solutions of linear equations for
  a variable (`x` by `40 - n`) are recorded as `solved` and inlined into polynomials, as the chains did.
- **Closed side conditions are looked up** before they are decided (`Rewrite.known`): a closed instance that is
  congruent to a fact modulo the classes holds; an instance with binders, e.g. an `invs`, holds if its canonical form
  equals that of a fact after both are normalized under the classes (`Classes.normalize`, registered subterms
  replaced by the roots of their classes), so the fresh list variables and identifying equations (`Js2 == Js`) that
  the simplifier needs for such conditions are not needed here.
- **Views of traces with several accumulators** ([`Views`](../src/cuvee/prove/Views.scala), see [teq.md](teq.md),
  "State traces"): the reads of the components of such a trace `S`, `current(S).i` and `⌊S⌋.i` (also through
  `earlier(j, ⌊S⌋.i)`), are markers that the matcher matches modulo their view, the same read of the projection of
  `S` to the component: the trace of that accumulator alone, the other accumulators bound over the histories `⌊S⌋.j`
  of their components (`Views.project`, syntactic). The histories are inert as dependencies, never rewritten in place,
  so the projections do not unfold each other; a component is not projected inside its own view (suspension by the
  loop and the component), and a marker is replaced by its view once that reads no component of `S` (the counter of a
  loop by its value). The `self` of a context, a list of pairs, maps `⌊X⌋`, the histories `⌊S⌋.j` and the history of
  the own component of a projection to their accumulators (`Views.selfOf`, `Views.relation`, by position), so that the
  invariants over the histories bound the accumulators (`Simplify.invariants`). A view is simplified under the facts of
  its position that mention a variable of the view (`Context.restricted`) and memoized by exactly those facts, so that
  positions that differ in other facts, e.g. the sibling conjuncts of the goal, share it soundly; `-debug views`
  reports the misses. The views are memoized by the marker, the bound variables and the
  classes, not by the full context: a view computed under weaker facts is reused.
- **Canonical forms** ([`Canon`](../src/cuvee/prove/Canon.scala)): `Canon.term` renames the variables bound inside
  a term by their depth, sorts the dependencies of combinators (their bound variables permuted along), the cases of
  choices, conjuncts, disjuncts and the sides of equations, so alpha-variants and reorderings coincide; `eq_` decides
  two terms with binders equal by it, which merges cases and dependencies modulo renaming. The traversal renames bound
  variables apart from the context, so positions that differ only by those names recur; the memos of the views, the reads and the facts
  of combinator contexts are keyed by the facts of the position under a renaming of its bound variables by position,
  and store their values under those names, from which the names of the position are restored. The combinator memo
  holds the facts of the inner context, from which the context is built at each position. The simplex checks are
  cached by the set of constraints and disequations (`Linear.checks`). Together they took the transpose from 22 s
  to 7 s.
- **One suspension facility** (`Context.active`): the rules whose side conditions are being evaluated (the
  re-entrance guard of the simplifier) and the components whose views are being computed, copied into the nested
  contexts; a memoized combinator context takes the suspended set of the position where it is reused.
- Programs, attributes and derivatives are not simplified; `-prove` is for the goals of `-teq` and `-teq-state`.

## Debugging

`-debug rewrite` prints the rewrite steps and the views (`view <marker> ~> <view>`); `-debug match` the matches that
went through the definition of a variable, the rules on traces whose left-hand side fails on a trace, with the case of
the expression that no case of the pattern covers and the guard that fails; `-debug conditions` the closed side
conditions that fail, with the `self` of the context and the facts on the condition's variables; `-debug simplify`
the steps of the traversal; `-rules` reports the rules applied per assertion as with `-simplify`. The compound
expressions of the core cache their hash (`Expr.hashCode`), since the memos and classes hash large terms at every
lookup.

## Checks

`scripts/prove/quick.sh` runs after each change (under 30 s: the state examples except the transpose against
their expected outputs, four per-variable examples that must leave no goal); `scripts/prove/slow.sh` runs on request
or before a commit (the transpose, the unit tests, the 30 algorithms of `examples/dafny/algorithms` in the state form
with their exit status, time and remaining goals, as the baseline for the work on them).

## State

Oct 13, 2026: the eleven examples of [examples/dafny/state](../examples/dafny/state) check under `-teq-state -prove`
with the module `state.dfy` alone (single loops, the swap of two arrays, five nested loops without fragment lemmas,
the transpose with one summary lemma, the syntax example), 1.5 to 3 s; the binary search leaves the exit open
(7 s). Open: forward facts for the bounds of named traces, lemmas over whole cycles in the matcher, the merge and the
sorts, the other frontends and the fallback for traces of several accumulators; see
[ideas/deduction-engine-implementation.md](../ideas/deduction-engine-implementation.md) and [TODO.md](../TODO.md).
