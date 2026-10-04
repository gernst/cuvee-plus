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
- The Dafny printer does not always print valid Dafny: indexed names are
  printed with unicode subscripts, e.g. `x₀`; the type parameters of assertions
  are omitted.
- The Dafny printer's `any` passes all values that are not results, commands,
  types, expressions or programs to the s-expression printer, which raises a
  `MatchError` on anything that is not an atom or a list of such:
  plain strings, lists of resolved expressions, e.g. the variables of a
  `modifies` attribute, and other values such as numbers
  ([dafny/Printer.scala](src/cuvee/dafny/Printer.scala)).
- SMT-LIB parser: imperative programs are not supported, `prog` always raises
  an error ([smtlib/Parser.scala](src/cuvee/smtlib/Parser.scala)).
- SMT-LIB parser: no `!` inside terms, `match`, `get-value`,
  `check-sat-assuming`, `echo`.
- Dafny `lemma` is not parsed, so lemmas and goals only come from SMT-LIB
  input (`lemma`, `goal`) and from `-verify`.
- Real arithmetic: decimal literals are typed `Real`, but no `Real` functions
  are declared in the preludes.
- Dafny containers `seq`, `set`, `multiset`, `map` are declared as sorts in the
  prelude but have no functions, and are not declared to the solver.
- Polymorphic declarations (`par`) are sent to z3/cvc5 as they are, which the
  solvers do not accept; they need monomorphization first.
- Dafny syntax for testers `Is` and type annotations `As`, e.g. `e.C?` and
  `e as T`: neither is parsed, and the Dafny printer raises an error
  ([dafny/Printer.scala](src/cuvee/dafny/Printer.scala)).
- Dafny: inside a `type` or `datatype` body, members must be accessed through
  `this`, e.g. `this.counter` and `this.m(a)`; a plain `counter` is an unknown
  expression, and a plain `m(a);` is only resolved for top-level methods.
  Names that are not local variables should be resolved as members of `this`
  (see [examples/stack.dfy](examples/stack.dfy)).
- Dafny: `var` declarations must come before the statements of a block.
- Termination in `Verify` and `Horn`: loops and procedures without
  `decreases` clause are not checked (Dafny guesses a measure), measures are
  integers only, and the measure of a procedure must refer to its inputs.
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


## Boogie frontend

- Procedures must be declared before they are called, so mutually recursive
  procedures are not supported ([boogie/Parser.scala](src/cuvee/boogie/Parser.scala)).
- Polymorphic functions and sorts reach the solvers unchanged, which reject
  them (see Bugs: monomorphization); `syntax.bpl` is therefore only parsed in
  the solver tests.
- No quantifiers over types, `forall<a> ...`.
- The SMT-LIB parser does not read `declare-var`, which the SMT-LIB printer
  writes for global variables, so SMT-LIB output with global variables cannot
  be read back.
- `Verify` and `Horn` treat all variables in `modifies` attributes as global
  variables, which holds for Boogie input (the parser checks it), but not
  for Dafny `modifies` clauses.
- `Horn` names the values of the global variables at the entry of a procedure
  `g$0, g$1, ...`, which may clash with names in the input.
- Printer: datatypes, `continue`, attributes of loops other than `invariant`
  and `modifies` (e.g. `decreases`), binders other than `forall` and `exists`,
  and literals other than integers and strings without `"` raise an error;
  goals and lemmas are printed as `goal` and `lemma`, which are not Boogie
  ([boogie/Printer.scala](src/cuvee/boogie/Printer.scala)).

## Additional transformations

- new folder `transform`
- `Flat` should specifically apply only to constrained horn clauses as generated by `Horn`: it should replace non-recursive datatypes with a single constructor by inlining them into the predicates
- `Split` should split proof goals from `Verify` into individual conjuncts of the form `forall ... anecedent ==> goal` or `!(exists...)`