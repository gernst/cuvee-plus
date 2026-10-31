# Implementations (`-implement`, `-instrument`)

Built-in sorts and functions (sets, sequences, maps) and declared functions can be given implementations that
programs are verified against; an implementation may be nondeterministic. Functions are implemented, by functions or
by methods (procedures); methods are not implemented. The code is
[transform/Implement.scala](../src/cuvee/transform/Implement.scala); open points are in
[ideas/datatype-verification.md](../ideas/datatype-verification.md), with the determinization of their
nondeterminism by an oracle.

## Modules and sorts

- Modules are injected by `-include implement:<name>` (`resources/cuvee/implement/<name>.dfy`) or `-include file`,
  after the entry `implement.dfy` (no declarations yet), before the input: they implement functions of the core, of
  the entry, or of themselves, not those of a client. The module so far is `renc` (maps and sets by the heap encoding
  Enc_R, see below).
- All their declarations carry `{:implement}`, hence `-known implement` drops them from the output.
- A datatype with `{:implement}` defines the sort of the prelude of the same name (`State.declare` lets it take the
  new attributes), e.g. `datatype {:implement} set<a> = set_(last_key: a, last_in: bool, version: int)` in `renc`.
  The types of the client do not change; equality becomes that of representations.

## Implementations

- `{:implement pattern}` on a function or method names the implemented function applied to a permutation of all
  inputs, `this` included, e.g. `{:implement k in this}` on the member `Contains(k, ctx)` of `set` in `renc`. Nothing
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
  `{:implement}`. Encodings use it to tell executions apart (`renc`); `-monomorph` instantiates the tuples, `-flat`
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
  implemented datatypes instead (e.g. `m - s` in `renc` reads `s.last_key`). `-implement` checks this: implemented
  functions in the bodies and contracts of implementations (except their patterns and contexts) are an error
  ([invalid_implement_body.dfy](../examples/dafny/transform/invalid_implement_body.dfy)).
- **Calls inside bodies stay calls,** also under `-instrument`, which inlines only the applications of clients.
- **Members must not shadow Dafny's:** a member method named `Values` would be called by `m.Values` of a client;
  hence `KeySet`, `ValueSet`.
- **Qualified static members:** `T.f(args)`; for sorts whose name is a keyword (`map`), the lowered name, `Map_f`.
- **Side branches:** a branch that ends in `assume false` only derives facts; `-chc` ends the path there.

## renc

[renc.dfy](../resources/cuvee/implement/renc.dfy) implements maps, sets, sequences, and multisets by Enc_R (Esen, Rümmer, Weber,
arXiv 2504.15844), for `-include implement:renc -instrument -chc -entry main -monomorph -flat -z3`; its header is the
reference, in short:

- **Encoding:** each map or set carries a prophecy key (`last_key`), its value (`last`), and whether it is in
  (`last_in`), plus its `version`; every observation (read, test) is numbered by the global `tick` and answered by a
  static predicate, `R` (values), `K` (tests of maps), `S` (tests of sets), which the run whose prophecy is the
  observed key asserts and every other run assumes. The arguments are the context, the number, and the answer.
- **Sequences and multisets** carry a prophecy index or element, its element or multiplicity, and their length or
  size as exact state (no version, no `N`): reads (and tests of multisets) are observations with the predicates `R`
  of sequences and `C` of multisets; stores, slices, extensions `s + [x]` and `m + multiset{x}` (of which displays
  are built), and lengths and sizes are exact functions; updates of multiplicities `m[x := n]` observe the old one
  for the size; concatenations and unions of multisets observe their right operand at the prophecy; intersections
  and differences of multisets choose their size within the bounds of the true one; `x in s`, prefixes, and
  submultisets are weak.
- **Operations:** reads, tests, stores, set updates `s[x := b]`, displays (stores or updates of the empty container,
  see the Dafny frontend), merges `m + n`, removals `m - s`, unions, intersections, differences, and `m.Keys` are exact;
  `m.Values`, `m <= n`, `s <= t`, `s < t` are constrained at the prophecy key only (sound, weak).
- **Sizes** are a predicate `N(version, z)` of the version, the number of the last change: changes derive it in side
  branches from the size before and their observation of the old membership, bulk operations within the bounds of the
  true size, and only reads of sizes assume it, such that loops do not depend on it.
- **Soundness** needs the predicates independent of the prophecy (hence static), an asserting run for every
  observation (also reads of absent keys), and a numbering by `tick` that does not depend on the prophecy.
- **Limits:** `tick` is reset by hand (`tick := 0`, `modifies tick`) in the examples; loops that count new keys
  (`|m| == n` after `n` new keys) are unknown to z3; deterministic programs only for completeness.

## Examples

- [dafny/transform/implement_method.dfy](../examples/dafny/transform/implement_method.dfy),
  [instrument.dfy](../examples/dafny/transform/instrument.dfy),
  [smtlib/transform/implement.smt2](../examples/smtlib/transform/implement.smt2),
  [instrument.smt2](../examples/smtlib/transform/instrument.smt2),
  [boogie/transform/implement.bpl](../examples/boogie/transform/implement.bpl),
  [instrument.bpl](../examples/boogie/transform/instrument.bpl).
- [dafny/renc](../examples/dafny/renc): reads, tests, displays, merges, removals, keys, sets and set updates, sizes,
  sequences (`seq_*`) and multisets (`multiset_*`; `multiset_ops` is unknown to z3 after 30 s, each operation alone is
  solved),
  loops (fills, counters, tests, insertions, overwrites), the context (`inputs.dfy`), the weak operations, and the
  conditions of soundness (`invalid_absent.dfy`, `invalid_merge.dfy`); the `invalid_*` examples are refuted.
