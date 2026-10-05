# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## New TODOs to be integrated, and instructions to address existing TODOs (provided by user)

- start with prioritizing this list by small things first, rewrite this file accordingly
- work on this list autonomously, if you have questions for which you'd like my input, defer the item and put a note in this file, keep this instruction when reordering the list

### Deferred (questions for the user)

- note on `Normalize` (from `cuvee.pure.Clause`): it is the last step of `Simplify` for assertions (not the first, since the antecedents are assumed in the context of the succedents during simplification anyway), since simplification and rewriting may produce nested implications and negations again, and normalization does not change normalized formulas. As in the original, `let` is turned into equations (exists among the antecedents, forall among the succedents), equations themselves are kept as they are, and a clause without succedents is the negation of its antecedents.

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
- The initial values of global variables, zero without initializer as in C,
  are the precondition of `main`, which the printer writes as an annotation
  `/*@ requires ...; */` that is not parsed; arrays cannot be initialized.
- `switch`, `goto`, pointers, structs, strings,
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
- The built-in sorts of Dafny that SMT-LIB lacks (`set`, `multiset`, `map`)
  are not in the output, the solver sinks declare them by themselves
  (`Solver.prelude`).
- Termination in `Verify` and `Horn`: loops and procedures without
  `decreases` clause are not checked (Dafny guesses a measure), measures are
  integers only, and the measure of a procedure must refer to its inputs.

## Code structure and consistency

- `core.Assoc` duplicates `easyparse.Assoc`.
- `send` and `receive` are recognized by their names (`Send`, `Recv`), and the
  history by the name of the global variable `history` (`Par.history`).
- The printers of Dafny and Boogie duplicate the mixfix logic (`prefix`,
  `infix`, `level`, and the precedences).

## Dafny frontend

- Lemmas and goals are single formulas, `lemma {:rw} φ` and `goal φ`, not
  Dafny's lemmas with parameters and contracts.
- Sets and multisets use cvc5's theories (`Set`, `Bag`), which z3 does not
  support; missing are set comprehensions, `multiset(s)` of a sequence,
  `m[x := n]` on multisets, and `>=`, `>`, disjointness `!!`. Maps (`map`)
  are declared as a sort but have no functions, since cvc5 has no theory of
  finite maps (they could be arrays together with a set as the domain).
- Sequences: no `seq(n, f)` or
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
  other than `invariant`, `modifies`, and `decreases`, binders other than
  `forall` and `exists`, derivatives, differential equations, and parallel
  composition; goals, lemmas, and `decreases` are printed as `goal`, `lemma`,
  and `decreases`, which are not Boogie
  ([boogie/Printer.scala](src/cuvee/boogie/Printer.scala)).

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
  i.e. `counter`, `current`, `steps`, `length`, `nth`, `earlier`, are declared
  by the lemma database of `-teq` ([resources/cuvee/teq.dfy](resources/cuvee/teq.dfy))
  only, whose names may clash with functions of the input; the database
  contains the lemmas that the rewrite engine can express, lemmas about `all`
  over a formula would need higher-order patterns; its polymorphic functions
  must be monomorphized for a solver.
- The combinators of trace equation systems are written
  `trace(e, for Y do x, y => u)`, `map(for Y yield y => u)`, and
  `all(for Y check y => φ)` in Dafny and Boogie, where updates with several
  cases are `if φ₁ then e₁, if φ₂ then e₂`, and like let in SMT-LIB,
  `(trace (x e) ((y Y)) u)`, `(map ((y Y)) u)`, `(all ((y Y)) φ)`, with
  `(cases (φ₁ e₁) (φ₂ e₂))`; `trace`, `map`, and `all` followed by `for` cannot
  be names of functions. The simplifier does not use the dependencies, e.g. it
  does not drop unused ones, and Split treats the combinators as atoms.
- The verifier by symbolic execution and trace equation systems (`-teq`,
  [verify/TEQ.scala](src/cuvee/verify/TEQ.scala)) generates high-level goals
  that contain the combinators for programs with loops, which must be
  rewritten by lemmas (`-teq -simplify` with the lemma database, which is
  small) or encoded into first-order logic (fall-back encodings,
  section 5.3 of the paper) before a solver can prove them. It does not
  support differential equations and parallel composition; loop invariants are ignored; the
  number of paths grows exponentially with the branches of a body.
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

### Proposal: Fourier-Motzkin in the simplifier

Fourier-Motzkin (FM) makes formulas simpler in the strict sense when it is used
as a decision procedure for comparisons: the results are `true` and `false`,
never larger terms. Only quantifier elimination may produce more constraints,
and should be restricted to the cases where it does not.

1. **Comparisons decided by the context.** `Ctx.lookup` is syntactic. At a
   comparison `0 <= p` or `0 < p` (the normal form of `Simplify.lt` and `le`),
   collect the linear constraints of the context: the comparisons among the
   assumptions, and the negated comparisons among the conclusions
   (`¬(0 <= p)` is `0 < -p`). If the context together with the negation of
   the comparison is unsatisfiable, the comparison is `true`; if it is
   unsatisfiable together with the comparison, it is `false`. E.g. under
   `0 <= i && i < n`, `i <= n` becomes `true` and `n < i` becomes `false`,
   which removes redundant guards and branches, also in the conjunctions and
   disjunctions of the goals of `-verify` and `-teq`, whose siblings are
   assumed by `nary`. Hook: `Ctx.constraints` and a call before the result of
   `lt`/`le` is built.
2. **Soundness on Int.** Unsatisfiability over the rationals implies
   unsatisfiability over the integers, so the verdicts of (1) are sound on
   `Int`, but incomplete. Tightening helps: on `Int`, `0 < p` is `1 <= p`, and
   a constraint whose coefficients have a common divisor `g` can round its
   constant down to a multiple of `g` (e.g. `2x <= 3` is `x <= 1`), which
   decides e.g. `0 < 2x && 2x < 2` as `false`.
3. **Inconsistent contexts.** When the linear assumptions are unsatisfiable,
   the context is marked inconsistent (`Ctx.inconsistent`), which the
   polarity mechanism already exploits, e.g. `x < y && y < x` is `false`.
4. **Redundant bounds.** As a consequence of (1) with `nary`, a conjunct that
   follows from the others is dropped, e.g. `x <= 3 && x <= 5` becomes
   `x <= 3`; dually for disjunctions.
5. **Quantifier elimination.** `exists x :: C(x)` for a conjunction of linear
   constraints is the result of eliminating `x`, exactly over `Real`, and over
   `Int` if all coefficients of `x` are `1` or `-1` (then `max l <= min u`
   has an integer witness); e.g. `exists x: real :: a < x && x < b` is
   `a < b`, and `∀ x. A(x) ⇒ B` with `x` not in `B` is `(∃ x. A(x)) ⇒ B`.
   This applies to the fresh variables of the goals of `-verify` and `-teq`
   (e.g. the values after a loop). The number of constraints grows from
   `l + u` to `l * u` for `l` lower and `u` upper bounds, hence only if
   `l <= 1` or `u <= 1`, where it shrinks.
6. **Costs.** Atoms are the non-linear monomials and the applications of
   other functions, which is sound. The constraints of a context are few in
   practice; a limit on their number (e.g. 20) bounds the cost of the
   elimination, which is otherwise doubly exponential.

Suggested order: (1)–(3) first, since they only replace subterms by constants,
then (4) and (5).

## Bitvectors

`BitVec(n)` in `Type`, `(_ BitVec n)` in SMT-LIB, with literals `#b...`,
`#x...`, `(_ bvK n)`, and the functions of SMT-LIB (`BitVecs`), which are
instantiated for the widths of their arguments, where indexed functions are
named by their indexed identifier, e.g. `(_ extract 7 0)`. Open: the simplifier
has no rules for them (e.g. constant folding), and a width cannot be a
parameter of polymorphic declarations.

### Proposal: bitvectors in Dafny

- Types `bv8`, `bv32`, ... (Dafny's own), parsed as `BitVec(n)` and printed as
  such (done in the printer).
- Operators by overloading on the type of the first argument, where
  `Overload.impl` dispatches on `BitVec(n)` in addition to sort constructors
  and instantiates `BitVecs.fun` for the width: `+`, `-`, `*` (wrap-around,
  `bvadd`, `bvsub`, `bvmul`), `/`, `%` (unsigned, `bvudiv`, `bvurem`), `&`,
  `|`, `^` (`bvand`, `bvor`, `bvxor`), `!` and unary `-` (`bvnot`, `bvneg`),
  `<<`, `>>` (`bvshl`, `bvlshr`, whose shift amount is converted to the width),
  `<`, `<=`, `>`, `>=` (unsigned comparisons), and the members
  `x.RotateLeft(k)`, `x.RotateRight(k)` for literal `k`.
- Literals: in Dafny, `5` and `0xff` take the type of their context. Numeric
  literals would get a fresh type parameter instead of `Int`, which type
  checking resolves to `Int`, `Real` (for decimals), or `BitVec(n)`, and which
  defaults to `Int` if it remains open; `Lit` then needs its value converted
  (modulo `2^n`) once the type is known (in `Type.instantiate`).
- Conversions `x as int` and `n as bv8`, which SMT-LIB has as `bv2nat` and
  `(_ int2bv n)` (supported by z3 and cvc5), as overloaded applications of
  `As`.

### Proposal: bitvectors in Boogie

- Types `bv8`, ..., and literals `5bv8` (scanner: `[0-9]+ "bv" [0-9]+`).
- Concatenation `x ++ y` (an infix operator) and extraction `x[8:0]`, which is
  `(_ extract 7 0)` since Boogie's upper bound is exclusive, as a new form of
  map access with `:`.
- All other functions are declared by the input with the attribute
  `{:bvbuiltin "bvadd"}`, e.g. `function {:bvbuiltin "bvadd"} add8(x: bv8,
  y: bv8): bv8;`, which the parser resolves to the instance of `BitVecs.fun`
  for the declared argument types; the declaration is kept, such that the
  output prints back the same, and applications of the declared function are
  replaced by the instance, similar to overloading.

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
- The history, `send`, and `receive` are declared by
  [resources/cuvee/dafny/hybrid.dfy](resources/cuvee/dafny/hybrid.dfy),
  which `-hybrid` injects, where the values of events are fixed to `int`.
- Only calls may be composed, not arbitrary statements.
