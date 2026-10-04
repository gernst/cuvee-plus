# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## C frontend

Simple imperative integer programs in a subset of C, without memory
([c/](src/cuvee/c), see [examples/c](examples/c)): integer types are `Int`,
`_Bool` is `Bool`, arrays are values `Array Int T`, functions are procedures
with the output `result`, and the global variables modified by a function are
inferred from the call graph. Open:

- Contracts in ACSL-like comments, `//@ requires e;`, `/*@ ensures e; */`,
  `//@ loop invariant e;`, with `\result` and `\old(e)`; without them, only
  loop-free programs can be verified with `-verify`, others with `-chc`.
- Bounded integers and overflow (as assertions, or bitvectors), the semantics
  of out-of-bounds accesses, and arrays as values versus C's reference
  semantics for array parameters; the sizes of arrays are ignored.
- Calls are evaluated before the statement that contains them, which is not
  supported in loop conditions, in the right operand of `&&` and `||`, and in
  the branches of `?:`.
- Initialized global variables, `switch`, `goto`, pointers, structs, strings,
  and the preprocessor (its lines are skipped).
- The printer writes SMT-LIB's `div` and `mod`, which result from C's `/` and
  `%`, as calls, which do not parse back; the temporary variables for the
  results of calls inside expressions, `tmp_1, ...`, may clash with names of
  the input when printed and parsed again.
- z3 answers `unknown` for Horn clauses with division by variables
  ([examples/c/div.c](examples/c/div.c)).

## General

- Exceptions other than `cuvee.Error` (`MatchError`, `NoSuchElementException`,
  `NotImplementedError`, `NumberFormatException` from `digits.toInt`) are not
  caught by `Pipe.run` and crash the whole run
  ([pipe/Pipe.scala](src/cuvee/pipe/Pipe.scala)).
- Polymorphic functions are sent to z3/cvc5 as they are, which the solvers do
  not accept, unless `-monomorph` replaces them by their instances;
  polymorphic assertions (`par`) are not instantiated, and procedures are not
  monomorphized.
- `-print` takes the file extensions as names of the output languages,
  `smt2`, `dfy`, `bpl`, which is not documented in `-help`.
- The output of `-print smt2` for Dafny and Boogie input lacks the sorts and
  datatypes of the prelude of the frontend (e.g. `chan`, `event`, tuples),
  which the solver sinks declare by themselves (`Solver.prelude`), so the
  printed output cannot be passed to a solver directly.
- Termination in `Verify` and `Horn`: loops and procedures without
  `decreases` clause are not checked (Dafny guesses a measure), measures are
  integers only, and the measure of a procedure must refer to its inputs.
- `old(e)` (`core.Old`) inside preconditions refers to the current values.
- Add a cache of further commonly used information to `State`
  ([core/State.scala](src/cuvee/core/State.scala)).

## Code structure and consistency

- Traversals of expressions and programs are written out repeatedly:
  `Subst`, `Overload.apply`, `Old.elim`, `Flat`;
  a generic map over the immediate subexpressions and subprograms would
  remove most of them.
- The operations on sequences (`Fun.seq`) have no sugar objects, unlike
  arithmetic (`Plus.int` etc.); `Mod.int` is `Sugar.associative`, but `mod` is
  not associative.
- `core.Assoc` duplicates `easyparse.Assoc`.
- `send` and `receive` are recognized by their names (`Send`, `Recv`), and the
  history by the name of the global variable `history` (`Par.history`).
- The printers of Dafny and Boogie duplicate the mixfix logic (`prefix`,
  `infix`, `level`, and the precedences).

## Dafny frontend

- `lemma` is not parsed, so lemmas and goals only come from SMT-LIB input
  (`lemma`, `goal`) and from `-verify`.
- Containers `set`, `multiset`, `map` are declared as sorts in the prelude
  but have no functions.
- Sequences: no `<` (proper prefix), `!in`, `seq(n, f)`, or
  multi-dimensional updates. `s[i := v]` is `seq.update` of cvc5, which z3
  does not support, and z3's logic `HORN` has no sequences at all.
- Member access `x.f` and testers `x.C?` work on variables only, e.g.
  `h[i].chan` must be written `event_chan(h[i])`.
- Inside a `type` or `datatype` body, members must be accessed through
  `this`, e.g. `this.counter` and `this.m(a)`; a plain `counter` is an unknown
  expression, and a plain `m(a);` is only resolved for top-level methods.
  Names that are not local variables should be resolved as members of `this`
  (see [examples/stack.dfy](examples/stack.dfy)).
- `var` declarations must come before the statements of a block.
- The contract clauses of methods must be in the order `modifies`,
  `requires`, `ensures`, `assumes`, `commits`, `decreases`; Dafny allows any
  order.
- Chained comparisons, e.g. `0 <= i < n`, are not supported.
- Decimal literals are scanned greedily, so nested tuple selections such as
  `t.0.1` are scanned as `t` and `.` followed by the literal `0.1`.
- The printer does not always print valid Dafny: indexed names are printed
  with unicode subscripts, e.g. `x₀`; the type parameters of assertions are
  omitted.
- The printer's `any` passes all values that are not results, commands,
  types, expressions, programs or lists of expressions to the s-expression
  printer, which raises a `MatchError` on anything that is not an atom or a
  list of such, e.g. plain strings and numbers.

## Boogie frontend

- Procedures must be declared before they are called, so mutually recursive
  procedures are not supported ([boogie/Parser.scala](src/cuvee/boogie/Parser.scala)).
- No quantifiers over types, `forall<a> ...`,
  no sequences, no parallel composition.
- The printer raises an error on datatypes, `continue`, attributes of loops
  other than `invariant` and `modifies` (e.g. `decreases`), binders other than
  `forall` and `exists`, strings with `"`, derivatives, differential equations, and parallel
  composition; goals and lemmas are printed as `goal` and `lemma`, which are
  not Boogie ([boogie/Printer.scala](src/cuvee/boogie/Printer.scala)).

## SMT-LIB frontend

- Procedures, programs (`assign`, `call`, `block`, `while`, `iter`, `ode`,
  `par`, ...), `old`, `diff`, and `declare-var` are extensions of SMT-LIB in
  the form written by the printer; there is no `assert` statement in the
  printed form, which writes `spec`.
- No `match`, `get-value`, `check-sat-assuming`, `echo`; annotations `!`
  inside terms are parsed but discarded, e.g. `:weight` in models of z3.

## Solvers and robustness

- `Solver.scoped` always pops in `finally`: if the solver process died, the
  failing `pop` hides the original error
  ([smtlib/Solver.scala](src/cuvee/smtlib/Solver.scala)).
- The solver's stderr is never read, which can block the solver if it writes a
  lot to it ([util/Tool.scala](src/util/Tool.scala)).
- The exit status is always 0, even when goals fail or errors are reported
  ([Cuvee.scala](src/cuvee/Cuvee.scala)).
- Readers for input files and the output stream of `-o` are never closed.
- Quantified specifications over sequences often end in `unknown`, e.g. a
  predicate defined by `forall i :: ... h[i] ...` for `h + [e]`; inductive
  axioms work better (see [examples/par.dfy](examples/par.dfy)).

## Warnings

- The implicit conversion `String => Name` is used without enabling
  `scala.language.implicitConversions`, which causes many feature warnings
  (main and tests); enable it once in the build with `-language:implicitConversions`.
- Two deprecation warnings for `Long + String` in debug messages of
  [smtlib/Solver.scala](src/cuvee/smtlib/Solver.scala) (lines 30 and 44).

## Transformations

- `Flat` ([transform/Flat.scala](src/cuvee/transform/Flat.scala)) treats all
  uninterpreted functions with a boolean result as predicates, not only those
  generated by `Horn`; the names of the fields of predicate parameters, `x_sel`,
  may clash with other parameters of the same predicate.
- The simplifier simplifies the expressions in procedures without context,
  since assignments invalidate the facts known before them; facts such as the
  test of a branch could be used up to the first assignment to their
  variables. It has no rules for sequences.

- Fourier-Motzkin elimination
  ([simplify/FourierMotzkin.scala](src/cuvee/simplify/FourierMotzkin.scala))
  decides linear constraints over the rationals, but is not used yet, e.g. by
  the simplifier for the comparisons in its context; it is incomplete over the
  integers.

## Hybrid programs

Non-standard features from Platzer's dL, as part of the Dafny frontend
(see [examples/hybrid.dfy](examples/hybrid.dfy)):

- The derivatives of formulas from `Verify` for the invariants of `Ode` must
  be simplified (`-simplify`) before the goals can be passed to a solver.
- The simplifier computes derivatives
  ([simplify/Simplify.scala](src/cuvee/simplify/Simplify.scala), `diff`);
  open are the chain rule for applications of other functions (where do their
  partial derivatives come from?), division, equations, and other formulas,
  which are kept as `Diff`.
- The derivatives computed by the simplifier introduce primed variables `x'`,
  which are bound by `Verify` for the differential cuts, but are free and not
  declared for derivatives written in the input, e.g. `(x, v :: e)'` in a
  method body.

## Parallel composition

Parallel composition of calls, whose assumption-commitment contracts are over
a global history of events (see [examples/par.dfy](examples/par.dfy)):

- `Horn` raises an error on `parallel`, and ignores assumptions and
  commitments in the bodies of procedures.
- Assumptions and commitments are used only by `parallel`: a call outside of
  `parallel` neither establishes the callee's assumption, which its body
  assumes initially, nor guarantees its commitment; this is unsound if such a
  procedure is called sequentially.
- The commitment is checked only at `send` and `receive` directly in the body,
  not at those inside other procedures called by it.
- A procedure may assume its assumption only initially, not after `receive`,
  where the environment extends the history.
- The history is declared by the input together with `send` and `receive`,
  since the value type of the events is fixed per program; the contracts of
  `send` and `receive` are not checked against their intended meaning.
- Only calls may be composed, not arbitrary statements.
