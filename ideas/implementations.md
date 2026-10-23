# Implementations of datatypes and functions

A plan to give the built-in sorts and functions (sets, sequences, maps, and declared functions) concrete
implementations that programs are verified against, where an implementation may be nondeterministic. Functions are
implemented, by functions or by methods; methods are not implemented. Implemented in 0.49.0 to 0.49.3 (Oct 22-23,
2026) and since (see "State" below).

## Modules

- The implementations are Dafny files in `resources/cuvee/implement/<name>.dfy`, injected by
  `-include implement:<name>` (or by `-include file.dfy` of the user). `-include <feature>:<name>` is generic over
  the features of `Config.features`: `teq` (entry `teq.dfy`, needs `-teq` or `-known teq`) and `implement` (entry
  `implement.dfy`, needs nothing, since a translation keeps the modules).
- As `teq.dfy` for the lemma database, the entry module `resources/cuvee/implement.dfy` declares what all
  implementations share. It is injected whenever an `implement` module is included or the feature is known
  (`Config.injected`). It is meant for the abstract functions that clients use and modules implement, e.g. a
  `choose<a>(s: set<a>): a` with its free lemma `|s| > 0 ==> choose(s) in s`: the modules are injected before the
  input, hence they can only implement functions of the core, of `implement.dfy`, and of themselves, not those of a
  client. It declares nothing yet.
- All declarations of the modules carry `{:implement}`, with or without a pattern, hence `-known implement` drops
  them from the output (`Sink.known` tests the keyword, not the value), as `-known teq` drops the lemma database.

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

## Implementations

- An implementation carries `{:implement <pattern>}`: the implemented function applied to a permutation of all
  inputs of the implementation, `this` included, written in the frontend's syntax and resolved in the scope of the
  inputs, e.g. `x in this` for `set.member(x, this)`, `this + t` for `seq.++`, `|this|`, `some(s)`. No general terms
  are matched: the pattern only names the implemented function and the position of each argument. Not an
  application, an argument that is not an input, a repeated or a missing input are errors.
- It is a member of the datatype, whose lowering puts `this` first, or a top-level declaration, e.g. for the
  functions without a receiver (`{}`, `{x}`, `[]`).
- **Implementations by functions** are deterministic; the result type of the function is that of the pattern.
- **Implementations by methods** may be nondeterministic: the method has a single output, of the type of the pattern,
  and a contract, a body, or both, e.g.
  `method {:implement some(s)} any(s: seq<int>) returns (x: int) requires |s| > 0 ensures x in s`. Each call
  chooses anew, since its output is havocked and constrained by the postcondition only; no determinization (an
  oracle input, a counter of evaluations) is needed.
- A function has at most one implementation.
- The refinement obligation: an implementation satisfies the axioms of the abstract function, for a method for every
  result its postcondition admits. It is a lemma of the module, proved, not assumed; it may be generated as a goal
  later.

## The transform `-implement`

A transformation of the task, hence optional: without it, a translation keeps the task as written, together with
the modules. Implementations are left as they are (all declarations with `{:implement}`).

1. **Implementations by functions** replace the applications of the implemented functions everywhere: in executed
   expressions, contracts, invariants, termination measures, assertions, function bodies, axioms, and lemmas. They
   must, since the abstract functions have no meaning on the datatype that now defines the sort.
2. **Implementations by methods** replace the applications in the expressions that procedure bodies execute: the
   right-hand sides of assignments, the arguments of calls, the tests of conditionals, the loop guards. Each
   application is lifted in front of its statement, in the order of evaluation, into a call
   `Call(any, args, List(test))` with a fresh local `test`, which replaces it:
   - the right operands of `&&`, `||`, `==>` and the branches of `ite` become conditionals when they contain
     applications, such that an application is evaluated only where the original evaluates it;
   - a loop guard with applications becomes `iter { calls; if !g break; body }`, whose invariants hold at the
     beginning of each iteration, before the calls of the guard;
   - the preconditions of the method are checked at the calls by `-vcgen`.
3. **Errors:** applications of functions implemented by methods in specifications (contracts, invariants,
   assertions, assumptions, termination measures, function bodies, axioms, lemmas, the attributes of blocks and
   loops), which are deterministic, under binders, which bind variables of the arguments, and under `old`, which
   evaluates them in another state.

## Semantics

- Each call of an implementation by a method chooses anew. The abstract function remains declared, but cannot be
  applied in specifications, since a deterministic reading (`some(s) == some(s)`) would not hold between two
  evaluations. Operations that a client means to be nondeterministic are methods with contracts, which are not
  implemented: they stay calls, checked by their contracts.
- Values are immutable: an observer never changes the representation of its receiver.

## Examples

[examples/dafny/transform/implement.dfy](../examples/dafny/transform/implement.dfy): the functions on sets
implemented by the functions of the module `listset` (sets as lists without duplicates), with `-include
implement:listset -known implement -implement`: `x in t` becomes `Set_member(t, x)` in contracts, function bodies, and
programs.

[examples/dafny/transform/implement_method.dfy](../examples/dafny/transform/implement_method.dfy): a function
`some(s)` implemented by a method `any(s)` with `requires |s| > 0 ensures x in s`; the client

```dafny
x := some(s) + some(s);
b := b && some(s) == x;
while b && some(s) < x { x := x - 1; }
```

becomes

```dafny
{ var test₁: int, test₂: int; test₁ := any(s); test₂ := any(s); x := test₁ + test₂; }
{ var test₅: bool;
  if b { var test₄: int; test₄ := any(s); test₅ := test₄ == x; } else { test₅ := false; }
  b := test₅; }
while * {
  var test₇: bool;
  if b { var test₆: int; test₆ := any(s); test₇ := test₆ < x; } else { test₇ := false; }
  if !test₇ { break; }
  x := x - 1;
}
```

## State

Implemented:

- 0.49.0: `-include <feature>:<name>` with `Config.features`, `Module`, `Feature`; `Attrs.isImplementation` and
  `State.declare` for sorts defined by an implementation.
- 0.49.1: Dafny annotations with values on functions, resolved in the scope of the inputs and checked against the
  result type (`Parser.annotations`), printed back by the Dafny printer, dropped by the SMT-LIB printer; annotations
  on `var`; the entry module, injected whenever a module of the feature is.
- 0.49.2: `-implement` for implementations by functions (`Implement`); the module `listset`; the examples
  `dafny/parsing/implement.dfy`, `invalid_annotation_value.dfy`, `invalid_implement_type.dfy`, and
  `dafny/transform/implement.dfy`.
- 0.49.3: `impl` and `implements` renamed to `implement` (attribute, feature, folder, entry, `Implement`).
- Not committed yet: implementations by methods: `{:implement pattern}` on methods with a single output, checked
  against its type; their applications lifted into calls in executed expressions; errors in specifications, under
  binders and `old`; the counter and the oracle removed from `implement.dfy`; the examples
  `dafny/transform/implement_method.dfy`, `invalid_implement_specification.dfy`, `invalid_implement_binder.dfy`.

To do:

- Shared abstract functions in `implement.dfy` (e.g. `choose` on sets) and implementations of them by methods in
  `listset`, once needed.
- Refinement obligations as goals.
- SMT-LIB attributes resolved as expressions, if modules in SMT-LIB are needed.

Not supported by decision: implementing methods, patterns other than a function applied to a permutation of the
inputs, determinization of nondeterministic implementations (oracle inputs, counters of evaluations), receivers
whose representation changes.
