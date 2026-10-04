# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## C frontend (plan)

A frontend for simple imperative integer programs in a subset of C, without
memory: no pointers, no `&`, no structs, no heap. Arrays are value types,
i.e., they are copied on assignment and passed by value, unlike in C.

Scope of the language:

- types `int`, `long`, `unsigned`, `char`, `_Bool`/`bool`, all mapped to `Int`
  (unbounded, first without overflow checks), and one-dimensional arrays
  `int a[n]`, mapped to `Array Int Int` (no length, bounds checks later);
- global variables and functions; parameters are mutable locals in C, which
  are copied into fresh locals since the inputs of procedures are fixed;
  the result is the output `result` of the procedure, and `return e;` is
  `result := e; return;`;
- statements: declarations with initializers, `=` and compound assignments
  (`+=`, `++`, ...) as statements only, `if`/`else`, `while`, `do`/`while`,
  `for` (desugared into `while`, where `continue` must still run the
  increment), `break`, `continue`, `return`, blocks;
- expressions with C precedence and C truth values: integers as conditions
  are compared to 0, comparisons and `&&`, `||`, `!` used as integers are
  `ite(b, 1, 0)`; `/` and `%` truncate towards zero, unlike SMT-LIB `div` and
  `mod`, and are translated by cases on the signs; calls only as the right
  hand side of assignments and as statements, otherwise they are lifted into
  temporaries (evaluation order as in the source);
- verification conventions of SV-COMP: `assert(e)`, `__VERIFIER_assume(e)`,
  `__VERIFIER_nondet_int()` (a havoc), `reach_error()`;
- contracts in ACSL-like comments, `//@ requires e;`, `/*@ ensures e; */`,
  `//@ loop invariant e;`, `//@ loop variant e;`, with `\result` and
  `\old(e)`;
- `modifies` attributes are not written in C: the global variables modified
  by a function are inferred from the call graph (transitively, also for
  recursion);
- preprocessor lines (`#include`, `#define`) are skipped first, later maybe
  simple constant macros.

Implementation, following the Boogie and Dafny frontends:

- `src/cuvee/c/`: `Scanner.flex` (jflex), `Syntax.scala`, `Grammar.scala`
  (easyparse, the mixfix parser with C's precedence table), `Parser.scala`
  (resolution into core, type checking by `state.exprs.check` and
  `state.progs.check`, which resolves overloading by `core.Overload`),
  `Printer.scala` (best effort, for `-print c`), `Source.scala`;
- a prelude `resources/cuvee/c/prelude.c` in the frontend's own syntax for the
  generic operators, like the other preludes;
- register the extension `.c` in [Config.scala](src/cuvee/Config.scala);
- examples `examples/c/*.c` with the first line `// expected: valid` or
  `// expected: invalid`, tests for parsing, the roundtrip through the
  printer, `-verify -z3`, and `-chc -z3`, as for Dafny.

Open questions: bounded integers and overflow (as assertions, or bitvectors),
the semantics of out-of-bounds accesses, and arrays as value types versus C's
reference semantics for array parameters.

## General

- Exceptions other than `cuvee.Error` (`MatchError`, `NoSuchElementException`,
  `NotImplementedError`, `NumberFormatException` from `digits.toInt`) are not
  caught by `Pipe.run` and crash the whole run
  ([pipe/Pipe.scala](src/cuvee/pipe/Pipe.scala)).
- Polymorphic declarations (`par`) of functions are sent to z3/cvc5 as they
  are, which the solvers do not accept; they need monomorphization first
  (polymorphic datatypes are accepted).
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
- Built-in functions are compared by equality of `Fun`, which includes the
  names of the formal parameters (`x$0, x$1, ...`); declarations with other
  names do not match the sugar.
- `send` and `receive` are recognized by their names (`Send`, `Recv`), and the
  history by the name of the global variable `history` (`Par.history`).
- The printers of Dafny and Boogie duplicate the mixfix logic (`prefix`,
  `infix`, `level`, and the precedences).

## Dafny frontend

- `lemma` is not parsed, so lemmas and goals only come from SMT-LIB input
  (`lemma`, `goal`) and from `-verify`.
- Containers `set`, `multiset`, `map` are declared as sorts in the prelude
  but have no functions.
- Sequences: whether `s[i]`, `s[i := v]` and `s[i..j]` are on sequences or
  arrays is decided by the type of `s` before type checking, which is
  unknown if it is a type parameter, e.g. `(if b then s else t)[0]`, and then
  falls back to arrays; no `<` (proper prefix), `!in`, `seq(n, f)`, or
  multi-dimensional updates. `s[i := v]` is `seq.update` of cvc5, which z3
  does not support, and z3's logic `HORN` has no sequences at all.
- Member access `e.f` works on variables only, e.g. `h[i].chan` must be
  written `event_chan(h[i])`.
- No syntax for testers `Is` and type annotations `As`, e.g. `e.C?` and
  `e as T`: neither is parsed, and the printer raises an error
  ([dafny/Printer.scala](src/cuvee/dafny/Printer.scala)).
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
- `a != b` is parsed as `!(a == b)` and printed like that.
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
- Polymorphic functions and sorts reach the solvers unchanged (see
  monomorphization above); `syntax.bpl` is therefore only parsed in the solver
  tests.
- No quantifiers over types, `forall<a> ...`, no decimal literals,
  no sequences, no parallel composition.
- The printer raises an error on datatypes, `continue`, attributes of loops
  other than `invariant` and `modifies` (e.g. `decreases`), binders other than
  `forall` and `exists`, literals other than integers and strings without `"`
  (e.g. reals), derivatives, differential equations, and parallel
  composition; goals and lemmas are printed as `goal` and `lemma`, which are
  not Boogie ([boogie/Printer.scala](src/cuvee/boogie/Printer.scala)).

## SMT-LIB frontend

- Imperative programs are not supported, `prog` always raises an error
  ([smtlib/Parser.scala](src/cuvee/smtlib/Parser.scala)), so the output of the
  printer for procedures cannot be read back, including the extensions
  `iter`, `ode`, `par`, `diff`, and `old`.
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
- `Split` should split proof goals from `Verify` into individual conjuncts of
  the form `forall ... antecedent ==> goal` or `!(exists ...)`.
- The simplifier works on assertions and function definitions only, not on
  the expressions in procedures, and has no rules for sequences.

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
- The primed variables in `Diff` are not declared, and the type checker does
  not check that they are in scope.

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
