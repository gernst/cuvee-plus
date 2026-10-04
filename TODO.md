# TODO

## General

- Exceptions other than `cuvee.Error` (`MatchError`, `NoSuchElementException`,
  `NotImplementedError`, `NumberFormatException` from `digits.toInt`) are not
  caught by `Pipe.run` and crash the whole run
  ([pipe/Pipe.scala](src/cuvee/pipe/Pipe.scala)).
- Polymorphic declarations (`par`) are sent to z3/cvc5 as they are, which the
  solvers do not accept; they need monomorphization first.
- Real arithmetic: real literals are rationals (`util.Rational`); the
  preludes declare arithmetic and comparison generically, which are resolved
  for `Int` and `Real` after type checking by
  [core/Overload.scala](src/cuvee/core/Overload.scala) in all frontends.
  Boogie has no decimal literals, and its printer raises an error on real
  literals.

- No `old(e)` in postconditions and loop invariants to refer to the values of
  global variables at the entry of a procedure, in Boogie and Dafny;
  `Horn` already names these values `g$i` in the postcondition predicates.
- Termination in `Verify` and `Horn`: loops and procedures without
  `decreases` clause are not checked (Dafny guesses a measure), measures are
  integers only, and the measure of a procedure must refer to its inputs.
- `Verify` and `Horn` treat all variables in `modifies` attributes as global
  variables, which holds for Boogie input (the parser checks it), but not
  for Dafny `modifies` clauses.
- `Horn` names the values of the global variables at the entry of a procedure
  `g$0, g$1, ...`, which may clash with names in the input.
- Add a cache of further commonly used information to `State`
  ([core/State.scala](src/cuvee/core/State.scala)).

## Dafny frontend

- `lemma` is not parsed, so lemmas and goals only come from SMT-LIB input
  (`lemma`, `goal`) and from `-verify`.
- Containers `seq`, `set`, `multiset`, `map` are declared as sorts in the
  prelude but have no functions, and are not declared to the solver.
- No syntax for testers `Is` and type annotations `As`, e.g. `e.C?` and
  `e as T`: neither is parsed, and the printer raises an error
  ([dafny/Printer.scala](src/cuvee/dafny/Printer.scala)).
- Inside a `type` or `datatype` body, members must be accessed through
  `this`, e.g. `this.counter` and `this.m(a)`; a plain `counter` is an unknown
  expression, and a plain `m(a);` is only resolved for top-level methods.
  Names that are not local variables should be resolved as members of `this`
  (see [examples/stack.dfy](examples/stack.dfy)).
- `var` declarations must come before the statements of a block.
- Decimal literals are scanned greedily, so nested tuple selections such as
  `t.0.1` are scanned as `t` and `.` followed by the literal `0.1`.
- The printer does not always print valid Dafny: indexed names are printed
  with unicode subscripts, e.g. `x₀`; the type parameters of assertions are
  omitted.
- The printer's `any` passes all values that are not results, commands,
  types, expressions or programs to the s-expression printer, which raises a
  `MatchError` on anything that is not an atom or a list of such:
  plain strings, lists of resolved expressions, e.g. the variables of a
  `modifies` attribute, and other values such as numbers.

## Boogie frontend

- Procedures must be declared before they are called, so mutually recursive
  procedures are not supported ([boogie/Parser.scala](src/cuvee/boogie/Parser.scala)).
- Polymorphic functions and sorts reach the solvers unchanged (see
  monomorphization above); `syntax.bpl` is therefore only parsed in the solver
  tests.
- No quantifiers over types, `forall<a> ...`.
- The printer raises an error on datatypes, `continue`, attributes of loops
  other than `invariant` and `modifies` (e.g. `decreases`), binders other than
  `forall` and `exists`, literals other than integers and strings without `"`,
  derivatives and differential equations; goals and lemmas are printed as
  `goal` and `lemma`, which are not Boogie
  ([boogie/Printer.scala](src/cuvee/boogie/Printer.scala)).

## SMT-LIB frontend

- Imperative programs are not supported, `prog` always raises an error
  ([smtlib/Parser.scala](src/cuvee/smtlib/Parser.scala)), so the output of the
  printer for procedures cannot be read back, including the extensions
  `iter`, `ode`, and `diff`.
- `declare-var` is not read, which the printer writes for global variables, so
  output with global variables cannot be read back.
- No `!` inside terms, `match`, `get-value`, `check-sat-assuming`, `echo`.
- The scanner does not read SMT-LIB 2.6 string escapes: a string ends at the
  first `"`, so a doubled `""` inside a string is not supported
  ([sexpr/Scanner.flex](src/cuvee/sexpr/Scanner.flex)). The printers already
  escape `"` as `""`.

## Solvers and robustness

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

## Transformations

- `Flat` ([transform/Flat.scala](src/cuvee/transform/Flat.scala)) treats all
  uninterpreted functions with a boolean result as predicates, not only those
  generated by `Horn`; the names of the fields of predicate parameters, `x_sel`,
  may clash with other parameters of the same predicate.
- `Split` should split proof goals from `Verify` into individual conjuncts of
  the form `forall ... antecedent ==> goal` or `!(exists ...)`.

## Hybrid programs

Non-standard features from Platzer's dL, as part of the Dafny frontend
(see [examples/hybrid.dfy](examples/hybrid.dfy)):

- `Iter(body, attrs)` ([core/Prog.scala](src/cuvee/core/Prog.scala)), loops
  with nondeterministic iterations, `while * { ... }` in Dafny and
  `while (*) { ... }` in Boogie, supported by `Verify` and `Horn`.
- `Ode(xs, rhs, dom, attrs)`, differential equations with an evolution
  constraint, `x', y' == e, f && dom invariant ...;` in Dafny, where `xs` are
  the variables without prime and the right hand sides bind tighter than `&&`.
- `Diff(xs, expr)` ([core/Expr.scala](src/cuvee/core/Expr.scala)), the
  derivative of `expr` with respect to `xs`, written `(x, y :: e)'` in Dafny;
  its free variables include the primed variables `x'` (`Var.primed`,
  `Name.primed`).

Open:

- `Verify` applies differential cuts for the invariants of `Ode` in sequence,
  followed by differential weakening; the resulting derivatives of formulas,
  `Diff(xs, phi)`, must be simplified before the goals can be passed to a
  solver. `Horn` will not support `Ode` and raises an error.
- `Diff` is not simplified yet, the simplifier only simplifies its argument.
- The primed variables in `Diff` are not declared, and the type checker does
  not check that they are in scope.
