# Implementations (`-implement`)

Built-in sorts and functions (sets, sequences, maps) and declared functions can be given implementations that
programs are verified against; an implementation may be nondeterministic. Functions are implemented, by functions or
by methods (procedures); methods are not implemented. The code is
[transform/Implement.scala](../src/cuvee/transform/Implement.scala); open points are in
[ideas/implement.md](../ideas/implement.md), the determinization of their nondeterminism in
[ideas/nondet.md](../ideas/nondet.md).

## Modules and sorts

- Modules are injected by `-include implement:<name>` (`resources/cuvee/implement/<name>.dfy`, e.g. `listset`, sets
  as lists without duplicates, `renc`, maps and sets by the heap encoding Enc_R for `-instrument`) or `-include file`, after the entry `implement.dfy` (no declarations yet). They are
  injected before the input, hence they implement functions of the core, of the entry, or of themselves, not those of
  a client.
- All their declarations carry `{:implement}`, hence `-known implement` drops them from the output.
- A datatype with `{:implement}` defines a sort of the prelude of the same name (`State.declare` lets it take the new
  attributes): `datatype {:implement} set<a> = Nil | Cons(head: a, tail: set<a>)`. The types of the client do not
  change; equality becomes that of representations.

## Implementations

- `{:implement pattern}` on a function or method names the implemented function applied to a permutation of all
  inputs, `this` included, e.g. `{:implement x in this}` on the member `member(x)` of `set`. Nothing more general is
  matched. The pattern is resolved in the scope of the inputs and checked against the result type, or the type of the
  single output of a method.
- Syntax: Dafny `{:implement x in this}`, Boogie `{:implement f(x)}` on functions and procedures, SMT-LIB and SV-LIB
  `:implement (f x)` on `declare-fun`, `define-fun`, `declare-proc`, and the body of `define-proc`. The SMT-LIB printer
  drops it on functions, whose declarations go to solvers.
- A function has at most one implementation. Members are lowered with `this` first; functions without a receiver
  (`{}`, `{x}`) are implemented at the top level.
- **Context** (Dafny only): `{:context ctx}` on an implementing method names an input that the pattern leaves out,
  which receives the context of the client at each application, the variables in scope there as a tuple (`true` for
  none, the variable for one, nested beyond the tuples of the prelude), except those that carry the state of
  implementations: variables of implemented sorts and global variables declared `{:implement}`
  (`Implement.context`). Encodings use it to tell executions apart, e.g. `renc` as the argument of its predicates
  (static members, polymorphic in the type of the context, see [static.dfy](../examples/dafny/parsing/static.dfy));
  `-monomorph` instantiates the tuples, `-flat` then flattens them.

## The transform

`-implement` is optional: without it, a translation keeps the task as written. Implementations themselves are left as
they are.

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

`-instrument` is `-implement` (one stage, `Config.instrument`), where the applications of functions implemented by
methods with a body become those bodies instead of calls, with the same attributes: a block whose locals are the
formal parameters renamed apart, with the type parameters instantiated, that assigns the arguments to the inputs,
asserts the precondition (the postcondition is not needed, the body is exact), keeps the global variables in locals if
the body has `old`, and assigns the output to the result; `return` in such a body is an error. The inlined methods
are dropped, methods without body are called. Encodings that instrument the program need it, e.g. `renc`, whose
generic methods would otherwise give polymorphic Horn clauses.

Examples: [dafny/transform/implement.dfy](../examples/dafny/transform/implement.dfy) (`listset`),
[implement_method.dfy](../examples/dafny/transform/implement_method.dfy),
[instrument.dfy](../examples/dafny/transform/instrument.dfy),
[dafny/renc](../examples/dafny/renc) (`renc` with `-instrument -chc -monomorph -flat`, `tick := 0` by hand: reads,
tests, displays, merges, removals, keys, sets, loops, the context of `inputs.dfy`, the weak operations on whole maps,
the soundness conditions of `invalid_absent.dfy` and `invalid_merge.dfy`),
[smtlib/transform/implement.smt2](../examples/smtlib/transform/implement.smt2),
[boogie/transform/implement.bpl](../examples/boogie/transform/implement.bpl), and for `-instrument`
[smtlib/transform/instrument.smt2](../examples/smtlib/transform/instrument.smt2),
[boogie/transform/instrument.bpl](../examples/boogie/transform/instrument.bpl).
