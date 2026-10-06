# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## New TODOs

- make a plan to resolve calls and selectors on this as well as on arbitrary terms, don't implement it
- check for stray references of Fun.... that are not goverened by syntactic sugar objects

## General

- Readers of input files and the stream of `-o` are never closed.
- `Match`: parsed and printed only in Dafny (expressions, without case
  conditions, not statements), no reduction on constructors, no rewriting
  modulo matches; SMT-LIB prints it only without case conditions.

## Code structure

- The printers of Dafny and Boogie duplicate the mixfix logic.
- `Verify.instance` eliminates `old(g)` in the postcondition of a callee by
  three substitutions with fresh placeholders `mod0`, since `Subst` also
  substitutes inside `old(e)`. A single traversal in `Verify` or `Old` that
  replaces the new values and strips `old(e)` would avoid them, but needs its
  own capture-avoiding handling of binders; `Subst` must not get a special
  case for this.
- Warnings: the implicit conversion `String => Name` without
  `-language:implicitConversions`.

## Solvers

- `Solver.scoped` pops in `finally`, which hides the original error if the
  solver died; its stderr is never read, which can block it.
- Axiomatization of data types: sequences are left to the solvers' theory,
  where quantified specifications often end in `unknown` (e.g. `positive` in
  [examples/hybrid/par.dfy](examples/hybrid/par.dfy)), whereas inductive
  axioms, as for datatypes, work better; sequences could be axiomatized
  inductively instead.

## Simplifier and rewriting

- Statements are simplified without context (assignments invalidate facts);
  tests of branches could be used up to the first assignment to their
  variables. No rules for sequences or bitvectors.
- Arithmetic on defined sorts (e.g. `type T = int`) is neither normalized nor
  matched, since `Ring` does not unfold them.
- Rewriting matches modulo A/C of `+` and `-` only (not `*`); all but the last
  variable of a sum take one summand or none, a negated last variable takes
  negative summands only; bound variables of combinators are not instantiated
  by conditional expressions; equations of the context are followed only for
  variables inside of the expression (`Ctx.eq`, rule `Subst` of the paper),
  not for terms such as `history.events == []`; innermost first, which may
  rewrite subterms before a rule for the whole term applies.
- The goal of [clock.dfy](examples/hybrid/clock.dfy) remains after
  `-simplify`: the rules of `delay` would need the fact `history.events == []`,
  and `exists s` would need to be instantiated by the time. Plan: replace
  quantified variables of record types, whose selectors occur in the body, by
  their constructor applied to fresh variables (as `Flat` does), with the
  reduction of selectors on constructors.
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
  and which inputs cannot use before `-teq` injects it. Lemmas about `invs`
  over a formula would need higher-order patterns.
- Counting `a[i] == v` over `⌊I⌋` yields `counts(0, v, maps(for ⌊I⌋ yield i => a[i]))`;
  there are no lemmas that relate such maps to `selects` or to `count` on
  sequences.

## Dafny frontend

- Containers: missing comprehensions, `multiset(s)`, the multiset update
  `m[x := n]`, `>=` and `>`, disjointness `!!`, `seq(n, f)`, and
  multi-dimensional updates.
- `x.f` and `x.C?` on variables only; members inside `type`/`datatype` bodies
  need `this.` ([examples/dafny/stack.dfy](examples/dafny/stack.dfy)).
- `var` declarations before statements; contract clauses in the fixed order
  `modifies`, `requires`, `ensures`, `assumes`, `commits`, `decreases`, for
  loops `modifies`, `invariant`, `decreases`.
- `t.0.1` is scanned as `t` `.` `0.1`.
- The printer writes unicode subscripts (`x₀`), and its `any` raises
  `MatchError` on plain strings and numbers.

## Boogie frontend

- Procedures must be declared before calls (no mutual recursion); no
  `forall<a>`, sequences, or parallel composition.
- Datatypes (`data`, not Boogie) have no testers and no `match`; `data`,
  `and`, and `|` are keywords.
- z3 answers `unknown` for Horn clauses over recursive datatypes
  ([examples/boogie/data.bpl](examples/boogie/data.bpl)).
- The `-chc` tests cover only [examples/boogie/horn](examples/boogie/horn),
  since the procedures of the other examples have contracts.
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
- `/` and `%` are translated to `div` and `mod` of SMT-LIB, which round down
  for a positive divisor, whereas C truncates towards zero
  ([examples/c/div.c](examples/c/div.c)); introduce C's division and
  remainder as proper functions in a C prelude.
- Calls inside loop conditions, right operands of `&&`/`||`, and branches of
  `?:` are not supported; temporaries `tmp_1, ...` may clash with input names.
- Initial values of globals become a `requires` annotation of `main` that is
  not parsed; arrays cannot be initialized.
- No `switch`, `goto`, pointers, structs, strings, preprocessor.
- The modifies clause of a loop is inferred from the core program, where a
  local variable that shadows a global one of the same type counts as global.
- z3 answers `unknown` for Horn clauses with division by variables
  ([examples/c/div.c](examples/c/div.c)), and for
  [examples/c/count.c](examples/c/count.c) since `incr_pre` is no longer
  `true` but inferred from the calls (only uncalled procedures are entry
  points).

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
  rule for other functions, no division (kept as `Diff`).
- Primed variables of derivatives written in the input are free and
  undeclared.

## Parallel composition

- `Horn` rejects `parallel` and ignores assumptions and commitments.
- Sequential calls neither establish the callee's assumption nor guarantee
  its commitment (unsound); commitments are checked only at `send`/`receive`/`tick`
  directly in the body.
- The type of histories with `send` and `receive` comes from `-hybrid`
  ([hybrid.dfy](resources/cuvee/dafny/hybrid.dfy)); the input declares the
  global `history`, and its results must be assigned to it, which is not
  checked.
- Only calls can be composed.
- Events are `message(chan, value)` or `time(time: real)`
  ([hybrid.dfy](resources/cuvee/dafny/hybrid.dfy)); `send` and `receive`
  produce messages, `tick` (`Tick`) time events by `delay`, also implicitly
  after each `ode` in `Verify`; neither `tick` nor `delay` has a test yet.
- `project(c, h)` (the values of the messages on `c`) is polymorphic with
  polymorphic axioms, which solvers are not expected to handle; the tests of
  hybrid programs (`VerifyHybrid`) therefore only generate the
  goals (`-print null`), and the examples are not expected to verify.
