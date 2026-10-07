# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## NEW

Then refactor the Dafny examples
- none should be top-level, all to be in sub-folders
- I suggest to rename the `bitvectors` subfolder to something like `language` and move all language-feature related tests there.
  The `decreases` test seems to be related to the vcgen.
- introduce a subfolder `teq` with the following examples, with correctness formulated as pre-/postconditions;
  don't attempt to solve/verify them in any way, don't produce tests yet, just the dafny files, don't add loop invariants, use explicit length variables, don't check array bounds, don't use `.Length` on arrays
  - simple counter loop, correctness: that the counter is n at the end
  - an array initialization loop with a symbolic value given as method input, asserting that all elements have that value
  - an array copy loop asserting copy
  - linear and binary search
  - swapping the contents of two arrays in a loop

## General

- The implementations of overloaded operators that are not part of cvc5
  (`seq.store`, `seq.member`, `seq.proper_prefixof`, `set.proper_subset`,
  `bag.select`, `bag.proper_subbag`, `map.store`, see `core.Overload`) are
  declared in the SMT-LIB prelude, but not defined, so the solvers reject
  them; definitions in terms of cvc5's functions are to be added, e.g. in
  the Dafny prelude. Until then, `examples/dafny/vcgen/seq.dfy` is not
  verified (`Examples.unsupported`), and the cvc5 tests of `seq.dfy`,
  `sets.dfy`, and `invalid_sets.dfy` are removed.
- Goals that do not hold are reported by the solver sink with their formula
  in SMT-LIB, not in the language of the input like the other reports.
- Readers of input files and the stream of `-o` are never closed.
- `Match`: parsed and printed only in Dafny (expressions, without case
  conditions, not statements), no reduction on constructors, no rewriting
  modulo matches; SMT-LIB prints it only without case conditions.
- Tests that run z3 have its default timeout of 1 s per query, which a
  loaded machine may exceed: `c.Translation.increments in expressions` failed
  with `unknown` while z3 unrolled a loop with the constant bound 10 (about
  0.17 s alone); with a symbolic bound it finds a linear invariant (0.035 s).

## Code structure

- The printers of C, Dafny, and Boogie duplicate `commas`, `braces`,
  `parens`, `atomic`, `level`, `doc(expr, context)`, `combinator`, and the
  mixfix logic; a shared trait for precedence-based printing would remove
  them. Their pattern `case _ if f(expr).isDefined => val Some(...) =
  f(expr): @unchecked` computes `f` twice; extractor objects would avoid it.
- `Monomorph` replays the whole prefix on every flush, quadratic for long
  incremental inputs; keeping the instances across flushes needs a
  transform with state, which `Stage` does not provide.
- No direct tests of easyparse (`Mixfix` precedences and associativity,
  `Repeat`, `Intersperse`) and of `simplify/Arith`.
- Warnings: the implicit conversion `String => Name` without
  `-language:implicitConversions`.

## Solvers

- The stderr of a solver is never read, which can block it.
- Axiomatization of data types: sequences are left to the solvers' theory,
  where quantified specifications often end in `unknown` (e.g. `positive` in
  [examples/hybrid/par.dfy](examples/hybrid/par.dfy)), whereas inductive
  axioms, as for datatypes, work better; sequences could be axiomatized
  inductively instead.

## Simplifier and rewriting

- Statements are simplified without context (assignments invalidate facts);
  tests of branches could be used up to the first assignment to their
  variables. No rules for sequences or bitvectors.
- Rewriting matches modulo A/C of `+` and `-` only (not `*`); all but the last
  variable of a sum take one summand or none, a negated last variable takes
  negative summands only; bound variables of combinators are not instantiated
  by conditional expressions; equations of the context are followed only for
  variables inside of the expression (`Chains.chain`, rule `Subst` of the paper),
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

## Dafny frontend

- Containers: missing comprehensions, `multiset(s)`, the multiset update
  `m[x := n]`, `>=` and `>`, disjointness `!!`, `seq(n, f)`, and
  multi-dimensional updates.
- `x.f` and `x.C?` on variables only; members inside `type`/`datatype` bodies
  need `this.` ([examples/dafny/stack.dfy](examples/dafny/stack.dfy)). The
  qualified name `T_f` comes from the declared sort of the variable, before
  type checking. Plan:
  1. testers `e.C?` on terms: the constructor determines the datatype
     (`state.exprs.is`), drop the restriction to variables;
  2. unqualified members in type bodies: with `this: T` in scope, `f(args)` is
     `T_f(this, args)` and `y := m(args)` calls `T_m(this, args)`, with
     Dafny's precedence: locals, members of `T`, top-level functions;
  3. functions and selectors on terms: the parser emits a generic
     application `.f` with fresh types and the receiver first, `Type.check`
     records it as pending, and `Overload.resolve` looks up `T_f` in
     `state.funs` by the sort of the receiver, extending `impl` by a lookup
     in the state; a receiver whose type is still a parameter is an error;
  4. method calls on terms (`y := f(x).m()`) need the receiver's sort when
     the statement is built: type check the receiver on its own, otherwise
     keep the restriction; last;
  5. tests: [stack.dfy](examples/dafny/stack.dfy) without `this.`, nested
     accesses `f(x).g()`, errors for unknown receivers.
- `var` declarations before statements; contract clauses in the fixed order
  `modifies`, `requires`, `ensures`, `assumes`, `commits`, `decreases`, for
  loops `modifies`, `invariant`, `decreases`.
- `t.0.1` is scanned as `t` `.` `0.1`.
- The printer's `any` raises `MatchError` on plain strings and numbers.
- Names that are neither identifiers nor operators, e.g. the instances
  `f<Int>` of `-monomorph`, are escaped by backticks, which the scanner reads
  back but Dafny does not have; names containing backticks are not handled.

## Boogie frontend

- Procedures must be declared before calls (no mutual recursion); no
  `forall<a>`, sequences, or parallel composition.
- Datatypes (`data`, not Boogie) have no testers and no `match`; `data`,
  `and`, and `|` are keywords.
- z3 answers `unknown` for Horn clauses over recursive datatypes
  ([examples/boogie/data.bpl](examples/boogie/data.bpl)).
- The printer rejects loop attributes other than `invariant`,
  `modifies`, `decreases`, other binders, derivatives, ODEs, and `par`;
  `goal`, `lemma`, `decreases`, `continue` are printed although not Boogie.

## C frontend

Subset of C without memory ([c/](src/cuvee/c), [examples/c](examples/c)).

- Unbounded integers, no overflow; arrays are values, sizes are ignored.
- [c/Parser.scala](src/cuvee/c/Parser.scala) (about 830 lines) mixes the
  resolution of expressions and statements, the inference of modifies
  (`assigned`, `effects`, `calls`, `writes`), and that of the translation
  unit, which could be split.
- No `switch`, `goto`, structs, floating point, bitwise operators,
  preprocessor; pointers only as arrays allocated by `malloc`, `alloca`,
  `calloc` (see [SV-COMP.md](SV-COMP.md)), and otherwise as values of `Ptr`
  in the prelude of C ([prelude.bpl](resources/cuvee/c/prelude.bpl)), which
  are compared but not dereferenced; no `&`, `*p`, or pointer arithmetic.
- The modifies clause of a loop is inferred from the core program, where a
  local variable that shadows a global one of the same type counts as global.
- z3 answers `unknown` for Horn clauses with division by variables
  ([examples/c/div.c](examples/c/div.c)), and for calls in loops whose
  callee has no goals, since its precondition is inferred from the calls
  (only uncalled procedures are entry points).

## SV-COMP task definitions

- The properties and expected verdicts of a task (`Task.properties`) are read
  but not used; only a single input file in C is supported.

## Bitvectors

`BitVec(n)` with the SMT-LIB literals and functions (`BitVecs`). Open: no
simplifier rules; widths cannot be parameters.

- Return to the bitvectors of Dafny: the test suites over
  `examples/dafny/vcgen` (`SimplifyPrograms`, `Verify`, `Split`) reported
  "goal does not hold" for [bitvectors.dfy](examples/dafny/bitvectors/bitvectors.dfy)
  sometimes in the full test run, depending on the tests run before it in the
  same JVM; alone, and with `java -jar cuvee.jar -simplify -verify -z3`, it
  passes. The fresh-name counters are reset per run (`Cuvee.pipe`), so some
  other state persists across runs. The example is moved out of `vcgen`,
  hence no suite runs it.

- Dafny: no `<<`, `>>` (as a token, `>>` would close nested type arguments
  `seq<seq<int>>`), no infix `|` (which clashes with `|s|`), no
  `RotateLeft/Right`, no `bv0`; `x as int < n` parses `int<` as type
  arguments, it needs parentheses.
- Boogie proposal: types `bv8`, literals `5bv8`, `x ++ y`, `x[8:0]` (exclusive
  upper bound), and functions declared with `{:bvbuiltin "bvadd"}` resolved to
  the instance of `BitVecs.fun`.

## Parallel composition

- `Horn` rejects `parallel` and ignores assumptions and commitments.
- Sequential calls neither establish the callee's assumption nor guarantee
  its commitment (unsound); commitments are checked only at `send`/`receive`/`tick`
  directly in the body.
- The results of `send`, `receive`, and `tick` must be assigned to the global
  `history`, which is not checked.
- Only calls can be composed.
- Neither `tick` nor `delay` has a test.
