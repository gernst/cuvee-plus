# TODO

## Bugs

- Exceptions other than `cuvee.Error` (`MatchError`, `NoSuchElementException`,
  `NotImplementedError`, `NumberFormatException` from `digits.toInt`) are not
  caught by `Pipe.run` and crash the whole run
  ([pipe/Pipe.scala](src/cuvee/pipe/Pipe.scala)).
- The scanner does not read SMT-LIB 2.6 string escapes: a string ends at the
  first `"`, so a doubled `""` inside a string is not supported
  ([sexpr/Scanner.flex](src/cuvee/sexpr/Scanner.flex)). The printers already
  escape `"` as `""`.
- The Dafny printer is not implemented: all `lines` methods in
  [dafny/Printer.scala](src/cuvee/dafny/Printer.scala) are `???`.
- The SMT-LIB printer: `lines(prog)` does not handle `Spec`, `Choice`, `If` and
  `While` (the compiler warns that the match is not exhaustive).
- SMT-LIB parser: imperative programs are not supported, `prog` always raises
  an error ([smtlib/Parser.scala](src/cuvee/smtlib/Parser.scala)).
- SMT-LIB parser: no `!` inside terms, `match`, `get-value`,
  `check-sat-assuming`, `echo`, and `(as ...)` only for constants and constant
  arrays.
- Dafny `lemma` is not parsed, so lemmas and goals only come from SMT-LIB
  input (`lemma`, `goal`) and from `-verify`.
- Real arithmetic: decimal literals are typed `Real`, but no `Real` functions
  are declared in the preludes.
- Dafny containers `seq`, `set`, `multiset`, `map` are declared as sorts in the
  prelude but have no functions, and are not declared to the solver.
- Polymorphic declarations (`par`) are sent to z3/cvc5 as they are, which the
  solvers do not accept; they need monomorphization first.
- The printer does not add `(as ...)` annotations to ambiguous polymorphic
  constants, nor to abstract values from models such as `@U_0` (cvc5).
- Dafny: inside a `type` or `datatype` body, members must be accessed through
  `this`, e.g. `this.counter`; a plain `counter` is an unknown expression.
  Names that are not local variables should be resolved as members of `this`
  (see [examples/stack.dfy](examples/stack.dfy)).
- Dafny statements: calls to methods that are not members (`x := m(a);`),
  call statements without results, and initialized locals (`var x := e;`).
- No termination checking (`decreases`) in `Verify`.
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
- Readers for input files and the output stream of `-o` are never closed.

