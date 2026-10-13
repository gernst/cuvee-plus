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
  congruent to a fact modulo the classes holds. Instances with binders (`invs`) are compared syntactically for now.
- **Views of state traces** ([`Views`](../src/cuvee/prove/Views.scala), see [teq.md](teq.md), "State traces"): the
  reads of the components of a state trace are markers that the matcher matches modulo their simplified view, the
  per-variable projection; a component is not projected inside its own view (suspension), and a marker is replaced
  by its view once that reads no component. The views are memoized by the marker, the bound variables and the
  classes, not by the full context: a view computed under weaker facts is reused.
- **One suspension facility** (`Context.active`): the rules whose side conditions are being evaluated (the
  re-entrance guard of the simplifier) and the components whose views are being computed, copied into the nested
  contexts; a memoized combinator context takes the suspended set of the position where it is reused.
- Programs, attributes and derivatives are not simplified; `-prove` is for the goals of `-teq` and `-teq-state`.

## Debugging

`-debug rewrite` prints the rewrite steps and the views (`view <marker> ~> <view>`), `-debug match` the matches
that went through the definition of a variable, `-debug simplify` the steps of the traversal; `-rules` reports the
rules applied per assertion as with `-simplify`.

## State

Oct 13, 2026: the ten examples of [examples/dafny/state](../examples/dafny/state) close under `-teq-state -prove`
with the module `state.dfy` alone (single loops, the swap of two arrays, five nested loops without fragment lemmas,
the transpose with one summary lemma, 1.5 to 22 s). Open: the cost of the simplex rebuilt per check (the transpose
takes three times as long as under the simplifier of the branch `worktree-state-trace`), the per-variable examples
of `-teq` under `-prove`, canonical forms for the lookup of `invs` conditions, triggers; see
[ideas/deduction-engine-implementation.md](../ideas/deduction-engine-implementation.md) and [TODO.md](../TODO.md).
