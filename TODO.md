# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## New TODOs to be integrated, and instructions to address existing TODOs (provided by user)

- start with prioritizing this list by small things first, rewrite this file accordingly
- work on this list autonomously, if you have questions for which you'd like my input, defer the item and put a note in this file, keep this instruction when reordering the list

### Medium

- implement `Monomorph` without a separate class that has mutable state, use `Ref` from `util` instead
- Move method `.map()` that generically traverses an expression into `Expr`. Check all traversals in the code whether they can be written with this new function.
  Similarly introduce `.map()` for all other types. Don't attempt to formulate something more complex than a point-wise mapping generically, though, keep the latter as explicit recursions.
- add tuples to the types in the Dafny grammar
- add support for strings and decreases in the boogie printer
- the C printer should get some fake notation for quantifiers and trace combinators, it is not good to mix sexprs with C-like notation
- in the C frontend, initialized variables should give the initialization constraint for predicate `main_pre`
- wrap the combinators in the Dafny printer so that if a line break is necessary, the `check` is below `for` etc... and the subsequent line after `=>` is indented at least some spaces from the surrounding parentheses
- in Horn, write clauses with goal in head, not with head False
- in Horn, omit the separate entry predicate, just come from the precondition
- in Horn, for the Block exit, don't use a separate helper, and don't use the inline helper either, rather instantiate the respective exits for break, continue by hand, and after the body has been translated, so that the order of clauses is right. when there is no break, don't emit the corresponding predicate or clause, same for continue; check the loop case, too
- add checking of decreases clauses, if present, to Horn, but don't attempt to generate fresh predicates for well-founded orders, as that is not supported by solvers
- in Dafny parse goals like lemmas
- consider the attribute "free" on lemmas, which treats them like axioms in the Solver sink, conceptually, however, the intention is that they should follow from the rest of the theory, but we don't want to enforce a proof
- write a proposal what Fourier Motzkin could contribute to the simplifier: actually making things simpler? put this proposal into the TODO.md file
- check this splitter: `https://github.com/gernst/cuvee/blob/main/cuvee/src/cuvee/pure/Horn.scala` (don't mind the file name), and think if this helps you improve `Split.scala`
- add comments in places where you would comment yourself

### Large

- split the `prelude.*` files into two parts: one that is truly there just to describe what the SMT-Solver should know, i.e., those defintions that are not injected into the pipeline (call this `builtin.*`) and then into the `prelude.*` put all definitions that *are* needed. In Dafny, for example, this currently means the channel/history stuff, receive and send, and the tuple types.
- implement `if <phi> then <psi>` syntax in Dafny top-level `Assert(...)` commands to stand for `<phi> ==> <psi>` but with lowest precedence, i.e., the `else` should be optional there and implicitly `True`. please make sure that the grammar remains unambiguous, otherwise ask before making changes
- `TEQ.scala`: support break and continue in symex
- in the generated constraints for `TEQs` make sure that the trace equations don't occur twice, by re-arranging the formula correctly
- hook up trace terms to the simplifier
- implement support for trace combinators in the transforms
- have `TEQ.scala` inject lemmas from `teq.dfy`, which should be part of the resources as the lemma database, use a fresh dafny parser, and inject all commands, they can remain in the final output
- check the flattening operation in this `https://github.com/gernst/cuvee/blob/main/cuvee/src/cuvee/pure/Clause.scala` file, implement a similar normalization step as `Normalize` in `simplify`, and integrate it into `Simplify`. should it be the first or last step in `Simplify`? I'm not sure.
- implement Dafny's additional types set, etc using CVC5's notation if available, ensure the overloading reoslution works propertly
- add support for bitvector types as `case class BitVec(n: Int)` in `Type` and then integrate all bitvector functions. Start with the SMT-LIB parser, and make proposals for Dafny and Boogie in TODO.md

### Deferred (questions for the user)

- note on `n + 1 < m <==> n <= m`: this does not hold on Int (n = 0, m = 1), the correct forms are `n < m + 1 <==> n <= m` and `n + 1 <= m <==> n < m`, which are implemented (`Simplify.lt`, `Simplify.le`, with `Succ`)

- In `Rewrite`, when a match has been computed and it is ambiguous, i.e., more than one side condition holds, and they are not the same match, then raise an error. this should make the top-level interface return just a single expression
  - done: `Rewrite.step` and `Rewrite.apply` return a single expression (`Option`), the first rule and the first match that apply
  - question: matching modulo A/C of `+` and `-` is ambiguous for almost all rules with two variables in a sum or a comparison, e.g. `f(x - y) = g(y)` matches `f(a - b)` with the results `g(b)`, `g(-a)`, and `g(b - a)`, and `x < y` matches `a < b` with `p(a, b)`, `p(-b, -a)`, `p(0, b - a)`; an error would reject the tests `differences`, `comparisons`, `real comparisons`, and `neutral` of `test/simplify/Rewrite.scala`. Should the error be raised nevertheless (and these rules be rejected), or should the matching of sums be made deterministic first (e.g. variables take whole sides of comparisons, and summands in the order of the polynomial), and only the remaining ambiguities be errors?

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
- The temporary variables for the results of calls inside expressions,
  `tmp_1, ...`, may clash with names of the input when printed and parsed
  again.
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
- The output of `-print smt2` for Dafny and Boogie input lacks the sorts and
  datatypes of the prelude of the frontend (e.g. `chan`, `event`, tuples),
  which the solver sinks declare by themselves (`Solver.prelude`), so the
  printed output cannot be passed to a solver directly.
- Termination in `Verify` and `Horn`: loops and procedures without
  `decreases` clause are not checked (Dafny guesses a measure), measures are
  integers only, and the measure of a procedure must refer to its inputs.

## Code structure and consistency

- Traversals of expressions and programs are written out repeatedly:
  `Subst`, `Overload.apply`, `Old.elim`, `Flat`;
  a generic map over the immediate subexpressions and subprograms would
  remove most of them.
- `core.Assoc` duplicates `easyparse.Assoc`.
- `send` and `receive` are recognized by their names (`Send`, `Recv`), and the
  history by the name of the global variable `history` (`Par.history`).
- The printers of Dafny and Boogie duplicate the mixfix logic (`prefix`,
  `infix`, `level`, and the precedences).

## Dafny frontend

- Lemmas are single formulas, `lemma {:rw} φ`, not Dafny's lemmas with
  parameters and contracts; goals are not parsed.
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
  (see [examples/dafny/stack.dfy](examples/dafny/stack.dfy)).
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
  axioms work better (see [examples/dafny/par.dfy](examples/dafny/par.dfy)).

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

- The functions on traces other than `butlast` (`⌊X⌋` in Dafny and Boogie),
  i.e. `counter`, `current`, `steps`, `length`, `nth`, `earlier`, are not
  declared by the preludes, since their names would clash with functions of
  the input; hence the goals of `-teq` do not parse back.
- The combinators of trace equation systems are written
  `trace(e, for Y do x, y => u)`, `map(for Y yield y => u)`, and
  `all(for Y check y => φ)` in Dafny and Boogie, where updates with several
  cases are `if φ₁ then e₁, if φ₂ then e₂`, and like let in SMT-LIB,
  `(trace (x e) ((y Y)) u)`, `(map ((y Y)) u)`, `(all ((y Y)) φ)`, with
  `(cases (φ₁ e₁) (φ₂ e₂))`; `trace`, `map`, and `all` followed by `for` cannot
  be names of functions. The simplifier, Monomorph, Flat, and the C printer do
  not support them yet.
- The verifier by symbolic execution and trace equation systems (`-teq`,
  [verify/TEQ.scala](src/cuvee/verify/TEQ.scala)) generates high-level goals
  that contain the combinators for programs with loops, which must be
  rewritten by lemmas (a database is missing, and the rewrite engine is not
  connected to `-teq`) or encoded into first-order logic (fall-back encodings,
  section 5.3 of the paper) before a solver can prove them. It does not
  support `break`, `continue`, `return` inside of loops, differential
  equations, and parallel composition; loop invariants are ignored; the
  number of paths grows exponentially with the branches of a body; the trace
  equation system of a loop occurs twice in the goal (safety of the body and
  exit).
- The rewrite engine ([simplify/Rewrite.scala](src/cuvee/simplify/Rewrite.scala))
  is applied by the simplifier after each round with the rewrite rules, the
  assertions and lemmas with the attribute `:rw` (`{:rw}` in Dafny and
  Boogie); it matches modulo A/C of `+` and `-` only (not `*`),
  where all but the last variable of a sum take a single summand or none, and
  it does not instantiate the bound variables of the combinators by
  conditional expressions or follow equations from the context (rule
  `Subst` of the paper); rewriting is innermost first, which may rewrite
  subterms before a rule for the whole term applies.
- Fourier-Motzkin elimination
  ([simplify/FourierMotzkin.scala](src/cuvee/simplify/FourierMotzkin.scala))
  decides linear constraints over the rationals, but is not used yet, e.g. by
  the simplifier for the comparisons in its context; it is incomplete over the
  integers.

## Hybrid programs

Non-standard features from Platzer's dL, as part of the Dafny frontend
(see [examples/dafny/hybrid.dfy](examples/dafny/hybrid.dfy)):

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
a global history of events (see [examples/dafny/par.dfy](examples/dafny/par.dfy)):

- `Horn` raises an error on `parallel`, and ignores assumptions and
  commitments in the bodies of procedures.
- Assumptions and commitments are used only by `parallel`: a call outside of
  `parallel` neither establishes the callee's assumption, which its body
  assumes initially, nor guarantees its commitment; this is unsound if such a
  procedure is called sequentially.
- The commitment is checked only at `send` and `receive` directly in the body,
  not at those inside other procedures called by it.
- The history is declared by the input together with `send` and `receive`,
  since the value type of the events is fixed per program; the contracts of
  `send` and `receive` are not checked against their intended meaning.
- Only calls may be composed, not arbitrary statements.
