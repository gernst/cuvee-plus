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
- The Dafny printer ([dafny/Printer.scala](src/cuvee/dafny/Printer.scala))
  prints operators like function calls, e.g. `+(x, 1)` and `!(p)`, until mixfix
  printing is done. Once it is, add a test that printing Dafny is stable when
  the output is parsed again, as for SMT-LIB.
- The Dafny printer does not always print valid Dafny: members are printed
  with their qualified name, e.g. `function counter.get(this: counter)`,
  instead of inside their type; indexed names are printed with unicode
  subscripts, e.g. `x₀`; the type parameters of assertions are omitted.
- The Dafny printer's `any` passes all values that are not results, commands,
  types, expressions or programs to the s-expression printer, which raises a
  `MatchError` on anything that is not an atom or a list of such:
  plain strings, lists of resolved expressions, e.g. the variables of a
  `modifies` attribute, and other values such as numbers
  ([dafny/Printer.scala](src/cuvee/dafny/Printer.scala)).
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
  `this`, e.g. `this.counter` and `this.m(a)`; a plain `counter` is an unknown
  expression, and a plain `m(a);` is only resolved for top-level methods.
  Names that are not local variables should be resolved as members of `this`
  (see [examples/stack.dfy](examples/stack.dfy)).
- Dafny: `var` declarations must come before the statements of a block.
- Dafny: let expressions `var x := e; body` should require explicit type
  annotations, `var x: T := e; body`. Currently `x` gets the type of `e`
  before type checking, so binding the result of a polymorphic function gives
  `x` an uninstantiated type parameter, and member access on `x` fails
  ([examples/members.dfy](examples/members.dfy) fails until this is done).
- No termination checking in `Verify`: `decreases` clauses are parsed and
  stored as `:decreases` attributes, one per component of the lexicographic
  measure, but not checked.
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

## Warnings

- The implicit conversion `String => Name` is used without enabling
  `scala.language.implicitConversions`, which causes about 190 feature warnings
  (main and tests); enable it once in the build with `-language:implicitConversions`.
- Two deprecation warnings for `Long + String` in debug messages of
  [smtlib/Solver.scala](src/cuvee/smtlib/Solver.scala) (lines 30 and 44).

