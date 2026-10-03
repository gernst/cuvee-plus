# TODO

## Bugs (reproduced)

- An unknown variable in a Dafny `modifies` clause crashes with
  `NoSuchElementException` instead of reporting an error: `contract` uses
  `scope.vars(_)` directly ([dafny/Parser.scala](src/cuvee/dafny/Parser.scala)).

## Bugs (found by reading the code)

- Exceptions other than `cuvee.Error` (`MatchError`, `NoSuchElementException`,
  `NotImplementedError`, `NumberFormatException` from `digits.toInt`) are not
  caught by `Pipe.run` and crash the whole run
  ([pipe/Pipe.scala](src/cuvee/pipe/Pipe.scala)).
- The preludes are loaded from paths relative to the working directory
  (`src/cuvee/smtlib/prelude.smt2`, `src/cuvee/dafny/prelude.dfy`), so
  `cuvee.jar` only works when run from the repository root. They should be
  loaded as classpath resources.
- The scanner does not read SMT-LIB 2.6 string escapes: a string ends at the
  first `"`, so a doubled `""` inside a string is not supported
  ([sexpr/Scanner.flex](src/cuvee/sexpr/Scanner.flex)). The printers already
  escape `"` as `""`.
- `Solver.sink` forwards `GetInfo`/`GetOption` with `ack`, so the solver's
  answer is reported as a "solver error"
  ([smtlib/Solver.scala](src/cuvee/smtlib/Solver.scala)).
- `State.define` for datatypes checks `sortdefs` instead of `datatypes` for
  "datatype already defined", reports the constructor's name instead of the
  selector's in "selector not declared", and does not check that a selector's
  argument is the datatype sort ([core/State.scala](src/cuvee/core/State.scala)).
- Dafny member access needs the base type to be known while resolving
  (`val Name(prefix, None) = base.typ.name`). It fails on results of
  polymorphic functions whose type is still a fresh parameter, and crashes with
  `MatchError` for indexed names ([dafny/Parser.scala](src/cuvee/dafny/Parser.scala)).
- Assignments to input parameters of procedures are not rejected, so
  postconditions in VCs may refer to the modified rather than the initial
  values ([chc/Verify.scala](src/cuvee/chc/Verify.scala),
  [core/Type.scala](src/cuvee/core/Type.scala)).

## Missing features

- The Dafny printer is not implemented: all `lines` methods in
  [dafny/Printer.scala](src/cuvee/dafny/Printer.scala) are `???`.
- The SMT-LIB printer: `lines(prog)` does not handle `Spec`, `Choice`, `If` and
  `While` (the compiler warns that the match is not exhaustive).
- SMT-LIB parser: imperative programs are not supported, `prog` always raises
  an error ([smtlib/Parser.scala](src/cuvee/smtlib/Parser.scala)).
- SMT-LIB parser: no `let`, `!` inside terms, `(as ...)`, `match`,
  `get-value`, `check-sat-assuming`, `echo`.
- Dafny `lemma` is not parsed, so lemmas and goals only come from SMT-LIB
  input (`lemma`, `goal`) and from `-verify`.
- Defined sorts (`define-sort`, Dafny `type T = ...`) are not unfolded during
  type checking, so a defined sort never unifies with its definition.
- Real arithmetic: decimal literals are typed `Real`, but no `Real` functions
  are declared in the preludes.
- Dafny containers `seq`, `set`, `multiset`, `map` are declared as sorts in the
  prelude but have no functions, and are not declared to the solver.
- Polymorphic declarations (`par`) are sent to z3/cvc5 as they are, which the
  solvers do not accept; they need monomorphization first.
- The printer does not add `(as ...)` annotations to ambiguous polymorphic
  constants.
- Dafny: inside a `type` or `datatype` body, members must be accessed through
  `this`, e.g. `this.counter`; a plain `counter` is an unknown expression.
  Names that are not local variables should be resolved as members of `this`
  (see [examples/stack.dfy](examples/stack.dfy)).
- Dafny statements: calls to methods that are not members (`x := m(a);`),
  call statements without results, and initialized locals (`var x := e;`).
- Procedure calls are not checked against the signature of the procedure in
  `Type.check` (only later by `Verify`, and only their number of arguments).
- No termination checking (`decreases`) in `Verify`.
- `Solver.sink` rejects `GetModel` and `Labels`.
- Add a cache of further commonly used information to `State`
  ([core/State.scala](src/cuvee/core/State.scala)).

## Robustness

- `Solver.scoped` always pops in `finally`: if the solver process died, the
  failing `pop` hides the original error
  ([smtlib/Solver.scala](src/cuvee/smtlib/Solver.scala)).
- The solver's stderr is never read, which can block the solver if it writes a
  lot to it ([util/Tool.scala](src/util/Tool.scala)).
- The exit status is always 0, even when goals fail or errors are reported
  ([Cuvee.scala](src/cuvee/Cuvee.scala)).
- Readers for input files and preludes, and the output stream of `-o`, are
  never closed.

