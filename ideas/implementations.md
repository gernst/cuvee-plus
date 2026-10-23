# Implementations of datatypes and functions

A plan to give the built-in sorts and functions (sets, sequences, maps, and functions declared by the input) concrete
implementations that programs are verified against, where an implementation may be nondeterministic. Only
functions are implemented, not methods. Parts are implemented in 0.49.0 (Oct 22, 2026, see "State" below); the
rest is not.

## Modules

- The implementations are Dafny files in `resources/cuvee/implement/<name>.dfy`, injected by
  `-include implement:<name>` (or by `-include file.dfy` of the user). `-include <feature>:<name>` is generic over the
  features of `Config.features`: `teq` (entry `teq.dfy`, needs `-teq` or `-known teq`) and `implement` (no entry, needs
  nothing, since a translation keeps the modules).
- As `teq.dfy` for the lemma database, a common entry module `resources/cuvee/implement.dfy` declares what all
  implementations share: the counter `var ticks: int` and the oracle `function nondet<a>(k: int): a`, which reads
  nondeterministic values. It is the entry of the feature `implement` in `Config.features`, injected before the modules
  of `-include implement:<name>`; unlike that of `teq`, it is injected whenever an `implement` module is, not only if the
  feature is known, since the feature needs nothing else (the condition of `Config.injected` becomes per feature).
- Whether the output drops a module's declarations is decided by their attributes, as for the preludes.

## Sorts

- A module defines a sort of the prelude by a datatype of the same name with `{:implement}`, e.g.
  `datatype {:implement} set<a> = Nil | Cons(head: a, tail: set<a>)`. The type of the client's variables does
  not change, only the meaning of the sort.
- `State.declare` lets a sort that is declared again with `:implement` (`Attrs.isImplementation`) and the same
  arity take the new attributes, such that the definition carries them and is printed rather than dropped with the
  prelude; `State.define` accepts a definition of a declared sort already.
- Equality on the sort becomes equality of representations, which coincides with that of the abstract values only
  for canonical representations. The use case is `-flat`, which inlines the datatypes; solvers' built-in names
  (`Set` in z3 and cvc5) are not a concern for now.

## Functions

- An implementation is a function with `{:implement <pattern>}`, either a member of the datatype, whose
  lowering puts `this` first, or a top-level function for the functions without a receiver (`{}`, `{x}`, `[]`).
- The pattern is a function applied to a permutation of the inputs of the implementation, `this` included, written
  in the frontend's syntax and resolved in the scope of the inputs, e.g. `x in this` for `set.member(x, this)`,
  `this + t` for `seq.++`, `|this|`. No general terms are matched: the pattern only names the implemented
  function and the position of each argument. Not an application, an argument that is not an input, a repeated
  or a missing input are errors.
- **Deterministic implementations** have exactly the inputs of the pattern.
- **Nondeterministic implementations** have one input more, which the pattern does not mention, of any type: a
  value that the transform supplies from an oracle and the implementation maps to its choice, e.g.
  `function {:implement choose(this)} choose(c: int): a requires this.Cons? { nth(c % card()) }`. Several
  choices take a tuple.
- The correctness of an implementation for the abstract axioms of the function is a lemma over its definition,
  for all oracle values, e.g. `s.Cons? ==> s.member(s.choose(c))`, proved, not assumed.

## The transform `-implement`

A transformation of the task, hence optional: without it, a translation keeps the task as written, together with
the modules.

1. **Deterministic implementations** replace the applications of the implemented functions everywhere: in
   executed expressions, in contracts, invariants, termination measures, assertions, function bodies, axioms, and
   lemmas, except in the module's own declarations. They must, since the abstract functions have no meaning on
   the datatype that now defines the sort.
2. **Nondeterministic implementations** replace applications in the expressions that programs execute only;
   elsewhere (specifications, function bodies, axioms) they are errors.
   - The occurrences of a statement are numbered in the order of evaluation, `0` to `n-1`: occurrence `i` becomes
     `f(args, nondet(ticks + i))`, followed by `ticks := ticks + n`. Occurrences in branches that are not
     evaluated (right operands of `&&`, `||`, `==>`, branches of `ite`) use up their numbers, which is harmless:
     only uniqueness matters.
   - `nondet<a>(k: int): a` of `implement.dfy` is uninterpreted and has no axioms, hence it cannot make the task
     inconsistent; `ticks` of `implement.dfy` is a global integer that only increases. The transform looks both up
     by name and reports their absence, e.g. `-implement` with an implementation module included by path that
     does not start from `implement.dfy`.
   - Loop guards: the guard is evaluated anew in each iteration, hence the loop increments `ticks` at the beginning
     of the body and after the loop, or becomes an `Iter` that breaks (see 3).
   - The procedures that evaluate such occurrences, directly or by calls (the call graph), get `ticks` in their
     `:modifies` and `ensures old(ticks) <= ticks`, such that a callee never uses values that the caller uses
     later; recursion is fine. The precedent is the global `history` of `-hybrid`.
3. **Preconditions** of implementations (`requires`) are asserted where they are evaluated in executed
   expressions, under the conditions of short-circuit evaluation (`assert guard ==> pre` before the statement);
   in a loop guard, the loop becomes `iter { assert ...; if !g break; ... }`, whose invariants hold at the
   beginning of each iteration, before the guard. In specifications they are not checked, as for any function.
4. Applications of nondeterministic implementations under binders and `old` are errors.

## Semantics

- Each evaluation of a nondeterministic implementation chooses anew, while the abstract function is a function:
  `choose(s) == choose(s)` holds in the client, not between two evaluations of the implementation. The client is
  correct under the implementation only if it relies on the axioms of the function alone, which hold for every
  oracle value (the lemma above). Operations that the client means to be nondeterministic are methods with
  contracts, which are not implemented: they stay calls, checked by their contracts.
- Values are immutable: an observer never changes the representation of its receiver. Sequencing the
  observations is the counter's job, external to the datatype.

## Example

The client, with an underspecified choice of its own:

```dafny
function choose<a>(s: set<a>): a
lemma choose_in<a>(s: set<a>) requires |s| > 0 ensures choose(s) in s

method sum(s0: set<int>) returns (r: int)
{
  var s := s0;
  r := 0;
  while |s| > 0
    invariant |s| <= |s0|
    decreases |s|
  {
    var x := choose(s);
    r := r + x;
    s := s - {x};
  }
}
```

The module, `-include implement:listset`:

```dafny
datatype {:implement} set<a> = Nil | Cons(head: a, tail: set<a>)
{
  function {:implement x in this} member(x: a): bool
  { this.Cons? && (head == x || tail.member(x)) }

  function {:implement |this|} card(): int
  { if this.Nil? then 0 else 1 + tail.card() }

  function {:implement this - t} minus(t: set<a>): set<a>
  { if this.Nil? then Nil else if t.member(head) then tail.minus(t) else Cons(head, tail.minus(t)) }

  // nondeterministic: c is supplied by the transform
  function {:implement choose(this)} choose(c: int): a
    requires this.Cons?
  { nth(c % card()) }

  function nth(i: int): a
    requires 0 <= i < card()
  { if i == 0 then head else tail.nth(i - 1) }
}

function {:implement {}} empty<a>(): set<a> { Nil }
function {:implement {x}} singleton<a>(x: a): set<a> { Cons(x, Nil) }

lemma choose_impl<a>(s: set<a>, c: int) requires s.Cons? ensures s.member(s.choose(c))
```

The client after `-implement`, members in member syntax:

```dafny
// var ticks: int and function nondet<a>(k: int): a from implement.dfy

method sum(s0: set<int>) returns (r: int)
  modifies ticks
  ensures old(ticks) <= ticks
{
  var s := s0;
  r := 0;
  while s.card() > 0
    invariant s.card() <= s0.card()
    decreases s.card()
  {
    assert s.Cons?;
    var x := s.choose(nondet(ticks + 0));
    ticks := ticks + 1;
    r := r + x;
    s := s.minus(singleton(x));
  }
}
```

## State

Implemented:

- 0.49.0: `-include <feature>:<name>` with `Config.features` (`teq`, `implement`), `Module`, `Feature`;
  `Attrs.isImplementation` and `State.declare` for sorts defined by an implementation.
- 0.49.1: Dafny annotations with values, `{:implement pattern}` on functions, resolved in the scope of the inputs
  and checked against the result type (`Parser.annotations`), printed back by the Dafny printer, dropped by the
  SMT-LIB printer; annotations on `var`; the entry module `resources/cuvee/implement.dfy` with `ticks` and `nondet`
  (`Implement.modules`), injected whenever an `implement` module is included or the feature `implement` is known
  (`Config.injected`).
- Not committed yet: `Implement` for deterministic implementations by functions, which replaces the first form by
  procedures: the patterns are checked (an application to distinct inputs, all of them or all but one), the
  applications replaced everywhere except in the implementations; the module `resources/cuvee/implement/listset.dfy`;
  the examples `dafny/parsing/implement.dfy`, `invalid_annotation_value.dfy`, `invalid_implement_type.dfy`, and
  `dafny/transform/implement.dfy`.

To do:

- Nondeterministic implementations in `Implement`: the counter and the oracle, the preconditions, `:modifies` and the
  monotonicity of `ticks` by the call graph.
- SMT-LIB attributes resolved as expressions instead of kept as s-expressions, if modules in SMT-LIB are needed.

Not supported by decision: implementing methods, patterns other than a function applied to a permutation of the
inputs, receivers whose representation changes.
