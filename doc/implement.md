# Implementations (`-implement`, `-instrument`)

Built-in sorts and functions (sets, sequences, maps) and declared functions can be given implementations that
programs are verified against; an implementation may be nondeterministic. Functions are implemented, by functions or
by methods (procedures); methods are not implemented. The code is
[transform/Implement.scala](../src/cuvee/transform/Implement.scala).

## Modules and sorts

- Modules are injected by `-include implement:<name>` (`resources/cuvee/implement/<name>.dfy`) or `-include file`,
  after the entry `implement.dfy` (no declarations yet), before the input: they implement functions of the core, of
  the entry, or of themselves, not those of a client.
- All their declarations carry `{:implement}`, hence `-known implement` drops them from the output.
- A datatype with `{:implement}` defines the sort of the prelude of the same name (`State.declare` lets it take the
  new attributes), e.g. `datatype {:implement} set<a> = set_(...)` defines the sort `set<a>`.
  The types of the client do not change; equality becomes that of representations.

## Implementations

- `{:implement pattern}` on a function or method names the implemented function applied to a permutation of all
  inputs, `this` included, e.g. `{:implement k in this}` on a member `Contains(k)` of `set`. Nothing
  more general is matched. The pattern is resolved in the scope of the inputs and checked against the result type, or
  the type of the single output of a method.
- Syntax: Dafny `{:implement x in this}`, Boogie `{:implement f(x)}` on functions and procedures, SMT-LIB and SV-LIB
  `:implement (f x)` on `declare-fun`, `define-fun`, `declare-proc`, and the body of `define-proc`. The SMT-LIB printer
  drops it on functions, whose declarations go to solvers.
- A function has at most one implementation. Members are lowered with `this` first, `static` members without it;
  functions without a receiver (`{}`, `{x}`, `map[]`, `map[k := v]`) are implemented at the top level.
- **Context** (Dafny only): `{:context ctx}` on an implementing method names an input that the pattern leaves out,
  which receives the context of the client at each application (`Implement.context`): the variables in scope there
  as a tuple (`true` for none, the variable for one, nested beyond the tuples of the prelude), except those that
  carry the state of implementations, i.e., variables of implemented sorts and global variables declared
  `{:implement}`. Encodings use it to tell executions apart; `-monomorph` instantiates the tuples, `-flat`
  then flattens them, in this order.

## The transform

`-implement` is optional: without it, a translation keeps the task as written. Implementations themselves are left as
they are, their bodies are not rewritten.

- **By a function:** every application is replaced, with the arguments at the positions of the pattern, also in
  contracts, invariants, function bodies, axioms, and lemmas.
- **By a method:** the method may choose its result nondeterministically, each call anew. Applications in executed
  expressions (right-hand sides, call arguments, tests, loop guards) are lifted into calls before their statement,
  in the order of evaluation, into fresh locals `test`; the right operands of `&&`, `||`, `==>` and the branches of
  `ite` become conditionals, a loop guard with calls becomes `iter { calls; if !g break; body }`, whose invariants
  hold before the calls.
- **Errors:** applications of functions implemented by methods in specifications (which are deterministic), under
  binders, and under `old`.
- **Backends:** a method with a contract is called by its contract in `-vcgen` and `-teq`; one with a body only is
  inlined in `-vcgen` and `-teq` and summarized in `-chc`.

**`-instrument`** is `-implement` (one stage, `Config.instrument`) with the same attributes, where the applications of
functions implemented by methods with a body become those bodies instead of calls: a block whose locals are the
formal parameters renamed apart, with the type parameters instantiated, that assigns the arguments to the inputs,
asserts the precondition (the postcondition is not needed, the body is exact), keeps the global variables in locals
if the body has `old`, and assigns the output to the result; `return` in such a body is an error. The inlined methods
are dropped, methods without body are called. Encodings that instrument the program need it: their generic methods
would otherwise give polymorphic Horn clauses.

## Writing modules

- **Implementations meet at representations:** since bodies are not rewritten, an implemented function applied in a
  body stays an uninterpreted function on representations, which is unsound; bodies read the fields of other
  implemented datatypes instead (e.g. an operation of maps on sets reads the fields of the set). `-implement` checks
  this: implemented functions in the bodies and contracts of implementations (except their patterns and contexts)
  are an error ([invalid_implement_body.dfy](../examples/dafny/transform/invalid_implement_body.dfy)).
- **Calls inside bodies stay calls,** also under `-instrument`, which inlines only the applications of clients.
- **Members must not shadow Dafny's:** a member method named `Values` would be called by `m.Values` of a client;
  hence e.g. `ValueSet`, not `Values`.
- **Qualified static members:** `T.f(args)`; for sorts whose name is a keyword (`map`), the lowered name, `Map_f`.
- **Side branches:** a branch that ends in `assume false` only derives facts; `-chc` ends the path there.

## Examples

- [dafny/transform/implement_method.dfy](../examples/dafny/transform/implement_method.dfy),
  [instrument.dfy](../examples/dafny/transform/instrument.dfy),
  [smtlib/transform/implement.smt2](../examples/smtlib/transform/implement.smt2),
  [instrument.smt2](../examples/smtlib/transform/instrument.smt2),
  [boogie/transform/implement.bpl](../examples/boogie/transform/implement.bpl),
  [instrument.bpl](../examples/boogie/transform/instrument.bpl).
