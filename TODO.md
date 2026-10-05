# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## New TODOs to be integrated, and instructions to address existing TODOs (provided by user)

- start with prioritizing this list by small things first, rewrite this file accordingly
- work on this list autonomously, if you have questions for which you'd like my input, defer the item and put a note in this file, keep this instruction when reordering the list

## General

- Exceptions other than `cuvee.Error` (`MatchError`, `NoSuchElementException`,
  `NumberFormatException`, ...) crash the run instead of being reported
  ([pipe/Pipe.scala](src/cuvee/pipe/Pipe.scala)).
- The exit status is always 0, even when goals fail or errors are reported.
- Readers of input files and the stream of `-o` are never closed.
- Polymorphic functions reach the solvers as they are unless `-monomorph`;
  polymorphic assertions and procedures are not monomorphized.
- Termination: loops and procedures without `decreases` are not checked,
  measures are integers, a procedure's measure must refer to its inputs.
- `Match`: no parsing in the frontends, no printing in Boogie and Dafny, no
  reduction on constructors, no rewriting modulo matches, no translation for
  solvers without `match`; SMT-LIB prints it only without case conditions.

## Code structure

- `core.Assoc` duplicates `easyparse.Assoc`.
- The printers of Dafny and Boogie duplicate the mixfix logic.
- `Arith.toPoly` and `Simplify.poly` duplicate the traversal of polynomials;
  `toPoly` could take a function for the leaves (identity for `Rewrite`,
  `simplify` for `poly`).
- `Verify.instance` eliminates `old(g)` in the postcondition of a callee by
  three substitutions with fresh placeholders `mod0`, since `Subst` also
  substitutes inside `old(e)`. A single traversal in `Verify` or `Old` that
  replaces the new values and strips `old(e)` would avoid them, but needs its
  own capture-avoiding handling of binders; `Subst` must not get a special
  case for this.
- `send`, `receive`, and the history are recognized by their names
  (`history_send`, `history_receive`, the global variable `history`).
- Warnings: the implicit conversion `String => Name` without
  `-language:implicitConversions`; two deprecations for `Long + String` in
  [smtlib/Solver.scala](src/cuvee/smtlib/Solver.scala).

## Solvers

- `Solver.scoped` pops in `finally`, which hides the original error if the
  solver died; its stderr is never read, which can block it.
- Quantified specifications over sequences often end in `unknown`, e.g.
  `positive` in [examples/dafny/par.dfy](examples/dafny/par.dfy), a quantifier
  over the events, although a hand-written version of its first goal is
  `unsat` in z3 and cvc5; inductive axioms work better.

## Simplifier and rewriting

- Statements are simplified without context (assignments invalidate facts);
  tests of branches could be used up to the first assignment to their
  variables. No rules for sequences or bitvectors.
- Rewriting matches modulo A/C of `+` and `-` only (not `*`); all but the last
  variable of a sum take one summand or none; bound variables of combinators
  are not instantiated by conditional expressions; equations of the context
  are not followed (rule `Subst` of the paper); innermost first, which may
  rewrite subterms before a rule for the whole term applies.
- Guards below combinators are matched syntactically first, so a bound
  variable that occurs only in guards may match any formula, e.g. `b` matches
  `!b`; lemmas whose guards are more specific must come first (as for
  `counts` in [teq.dfy](resources/cuvee/teq.dfy)).
- Fourier-Motzkin ([simplify/FourierMotzkin.scala](src/cuvee/simplify/FourierMotzkin.scala))
  is not used yet. Proposal, in this order:
  1. decide `0 <= p`/`0 < p` against the linear facts of the context (the
     comparisons among the assumptions, negated ones among the conclusions)
     in `Simplify.implied`/`denied`, sound on `Int` too, with tightening
     (`0 < p` is `1 <= p`, rounding by the gcd of the coefficients);
  2. mark contexts with unsatisfiable linear assumptions inconsistent;
  3. then redundant bounds vanish by `nary`, e.g. `x <= 3 && x <= 5`;
  4. eliminate `exists x` over linear constraints where the number of
     constraints does not grow (`l <= 1` or `u <= 1` bounds), exact on `Real`,
     on `Int` for coefficients ±1;
  5. limit the number of constraints (e.g. 20).

## Trace equation systems (`-teq`)

- The functions on traces are declared only by the lemma database
  ([teq.dfy](resources/cuvee/teq.dfy)), whose names may clash with the input,
  and which inputs cannot use before `-teq` injects it. Lemmas about `all`
  over a formula would need higher-order patterns.
- `trace`, `map`, `all` followed by `for` cannot be function names; Split
  treats the combinators as atoms.
- The goals contain the combinators and must be rewritten by lemmas or
  encoded into first-order logic (section 5.3 of the paper) for a solver. No
  differential equations or parallel composition; loop invariants are
  ignored; paths grow exponentially with the branches of a body.
- Counting `a[i] == v` over `⌊I⌋` yields `counts(0, v, map(for ⌊I⌋ yield i => a[i]))`;
  there are no lemmas that relate such maps to `selects` or to `count` on
  sequences.

## Dafny frontend

- Lemmas and goals are single formulas (`lemma <a> {:rw} φ`, `goal φ`), not
  Dafny's lemmas with parameters and contracts.
- Sets and multisets use cvc5's theories (not z3); missing comprehensions,
  `multiset(s)`, `m[x := n]`, `>=`, `>`, `!!`. `map` is a sort without
  functions. Sequences: no `seq(n, f)`, no multi-dimensional updates;
  `s[i := v]` is cvc5's `seq.update`; z3's `HORN` has no sequences.
- `x.f` and `x.C?` on variables only; members inside `type`/`datatype` bodies
  need `this.` ([examples/dafny/stack.dfy](examples/dafny/stack.dfy)).
- `var` declarations before statements; contract clauses in the fixed order
  `modifies`, `requires`, `ensures`, `assumes`, `commits`, `decreases`.
- `t.0.1` is scanned as `t` `.` `0.1`.
- The printer writes unicode subscripts (`x₀`), and its `any` raises
  `MatchError` on plain strings and numbers.

## Boogie frontend

- Procedures must be declared before calls (no mutual recursion); no
  `forall<a>`, sequences, or parallel composition.
- Datatypes (`data`, not Boogie) have no testers and no `match`; `data`,
  `and`, and `|` are keywords.
- z3 answers `unknown` for Horn clauses over recursive datatypes
  ([examples/boogie/data.bpl](examples/boogie/data.bpl) is skipped by the
  `-chc` test).
- The printer rejects loop attributes other than `invariant`,
  `modifies`, `decreases`, other binders, derivatives, ODEs, and `par`;
  `goal`, `lemma`, `decreases`, `continue` are printed although not Boogie.

## SMT-LIB frontend

- Programs, `old`, `diff`, `declare-var` are extensions in the printer's form.
- No `match`, `get-value`, `check-sat-assuming`, `echo`; annotations `!`
  inside terms are discarded.

## C frontend

Subset of C without memory ([c/](src/cuvee/c), [examples/c](examples/c)).

- No ACSL contracts (`//@ requires`, `loop invariant`, `\result`, `\old`), so
  only loop-free programs verify with `-verify`, others need `-chc`.
- Unbounded integers, no overflow; arrays are values, sizes are ignored.
- Calls inside loop conditions, right operands of `&&`/`||`, and branches of
  `?:` are not supported; temporaries `tmp_1, ...` may clash with input names.
- Initial values of globals become a `requires` annotation of `main` that is
  not parsed; arrays cannot be initialized.
- No `switch`, `goto`, pointers, structs, strings, preprocessor.
- z3 answers `unknown` for Horn clauses with division by variables
  ([examples/c/div.c](examples/c/div.c)).

## Bitvectors

`BitVec(n)` with the SMT-LIB literals and functions (`BitVecs`). Open: no
simplifier rules; widths cannot be parameters.

- Dafny proposal: types `bv8`, ...; operators by overloading on `BitVec(n)`
  (`+ - *` wrap-around, `/ %` unsigned, `& | ^ ! -`, `<< >>`, unsigned
  comparisons, `RotateLeft/Right`); numeric literals with a fresh type
  parameter that defaults to `Int`, converted modulo `2^n`; `as int`/`as bv8`
  as `bv2nat`/`int2bv`.
- Boogie proposal: types `bv8`, literals `5bv8`, `x ++ y`, `x[8:0]` (exclusive
  upper bound), and functions declared with `{:bvbuiltin "bvadd"}` resolved to
  the instance of `BitVecs.fun`.

## Hybrid programs

- Derivatives of `Ode` invariants need `-simplify` before a solver; no chain
  rule for other functions, no division or equations (kept as `Diff`).
- Primed variables of derivatives written in the input are free and
  undeclared.

## Parallel composition

- `Horn` rejects `parallel` and ignores assumptions and commitments.
- Sequential calls neither establish the callee's assumption nor guarantee
  its commitment (unsound); commitments are checked only at `send`/`receive`
  directly in the body.
- The type of histories with `send` and `receive` comes from `-hybrid`
  ([hybrid.dfy](resources/cuvee/dafny/hybrid.dfy)); the input declares the
  global `history`, and its results must be assigned to it, which is not
  checked.
- Only calls can be composed.
- Events are `message(chan, value)` or `time(time: real)`
  ([hybrid.dfy](resources/cuvee/dafny/hybrid.dfy)); `send` and `receive`
  produce messages only, nothing produces time events yet.
- `project(c, h)` (the values of the messages on `c`) is polymorphic with
  polymorphic axioms, which solvers are not expected to handle; the tests of
  hybrid programs (`VerifyOde`, `VerifyPar`) therefore only generate the
  goals (`-print null`), and the examples are not expected to verify.
