# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## Bugs

- A bound variable may capture a constant of the same name in the output of
  SMT-LIB: normalization renames bound variables apart from free variables,
  but constants (`declare-const x`) are functions, e.g.
  `(=> (exists ((x Int)) (< x y)) (<= x y))` becomes
  `(forall ((x Int)) (=> (< x y) (<= x y)))` with `-simplify`.
- Rewriting does not terminate on
  [standard_partial_init_ground.dfy](examples/sv-comp/array-examples/standard_partial_init_ground.dfy)
  with the lemmas of teq.dfy alone (a stack overflow, reported as such): the
  counter `j` of the agreeing indices is a `count` over a `maps` with the
  dependency `⌊I⌋`, the read `earlier(k, ⌊J⌋)` becomes a `count` over a
  `prefix` of it, whose simplification builds the context of the iterations
  again (`Simplify.iterations`), in which `earlier(k', ⌊I⌋)` is simplified,
  with fresh `k` each time.
- A rule whose left-hand side is a comparison of two open variables, e.g.
  `j < n` with a side condition `invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: P(k, h))`,
  overflows the stack before any step: it matches every comparison, also
  the bounds `0 <= k < n` of the iterations that matching the `invs` of the
  side condition assumes in the context of its body (`Simplify.combinator`),
  where the rule is tried again (see
  [standard_find_ground-1.dfy](examples/sv-comp/array-examples/standard_find_ground-1.dfy)).
- A side condition that is an equation between applications with a variable
  that is not instantiated yet, e.g. `prefix(n, xs) == prefix(n, ys)` with `n`
  open, is not matched against an equal hypothesis
  `prefix(N, t) == prefix(N, u)`, while `q(prefix(n, xs), prefix(n, ys))` and
  `xs == ys` are; reproduced with `-simplify` alone on a lemma
  `if prefix(n, xs) == prefix(n, ys) then (earlier(j, xs) == earlier(j, ys)) <==> true`
  (see [standard_compare_ground.dfy](examples/sv-comp/array-examples/standard_compare_ground.dfy),
  which uses the predicate `agree` instead).
- A pattern with two cases matches an update with a single case, which one
  case of the pattern covers (`Rewrite.matchesUpdates`); variables of the rule
  that occur only in the other case stay uninstantiated, and the rule is
  applied anyway: the lemma
  `trace(x0, ... :: case c => F(x, k, h) case !c => G(x, k, h)) == if c then trace(... F ...) else trace(... G ...)`
  rewrites `trace(a, ... :: x[h := x[h] + 2])` to
  `if true then trace(... F ...) else trace(... G ...)` with `G` free, which
  does not terminate (see [condm.dfy](examples/sv-comp/array-fpi/condm.dfy)).
- A sum that contains a bound variable of a combinator in a pattern is not
  matched, even against the same sum: the lemma
  `current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[k := a[k + -1]])) == hit(a0)`
  does not rewrite `current(trace(a2, for ⌊counter(0, 1, N)⌋ do a, k :: a[k := a[k + -1]]))`
  with `-simplify`, while `a[k := a[k] + d]` matches `a[k := a[k] + 6]`;
  recurrences over the previous element are not matched (see
  [ifcomp.dfy](examples/sv-comp/array-fpi/ifcomp.dfy)), only those whose
  index is a dependency, e.g. `⌊counter(1, 1, n)⌋` (see
  [eqn1.dfy](examples/sv-comp/array-fpi/eqn1.dfy)).
- `-teq` overflows the stack (an uncaught `StackOverflowError` in `Subst`) on
  a loop body with ten conditionals in sequence, presumably from the 2^10
  paths of its symbolic execution (see
  [diamond_2-2.dfy](examples/sv-comp/loop-acceleration/diamond_2-2.dfy)).

## General

- Function types (`arrow₁`, ...) and their applications (`apply₁`, ...)
  are printed and parsed in SMT-LIB as those of SMT-LIB 2.7, `(-> A B C)`
  and `(@ f a b)`; they are marked `{:ho}` and their declarations are not
  passed to solvers, which hardly support them.
  Lambdas of SMT-LIB are arrays of a single variable, since solvers support
  only those, hence lambdas of function type printed in SMT-LIB are not read
  back.
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
  [examples/dafny/hybrid/par.dfy](examples/dafny/hybrid/par.dfy)), whereas inductive
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
- The goal of [clock.dfy](examples/dafny/hybrid/clock.dfy) remains after
  `-simplify`: the rules of `delay` would need the fact `history.events == []`,
  and `exists s` would need to be instantiated by the time. Plan: replace
  quantified variables of record types, whose selectors occur in the body, by
  their constructor applied to fresh variables (as `Flat` does), with the
  reduction of selectors on constructors.
- Guards below combinators are matched syntactically first, so a bound
  variable that occurs only in guards may match any formula, e.g. `b` matches
  `!b`; lemmas whose guards are more specific must come first (as for
  `counts` in [teq.dfy](resources/cuvee/teq.dfy)).
- Variables that occur only in side conditions of rules or in guards of
  patterns are instantiated by matching the conjuncts against the facts of the
  context (`Context.known`, assumptions and negated conclusions as given, not
  chains or differences) or the conjuncts of the guard of the expression
  (`Rewrite.conditions`), in the order of the conjuncts; open comparisons and
  equations of side conditions are not searched, and the first match is taken
  among several.
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
- A lemma that is an equation of integers, e.g. `2 * s == n + n * n`, is a
  rule on its left-hand side as a term, not on the atom; equivalences of atoms
  work (see [gauss_sum.dfy](examples/sv-comp/loop-new/gauss_sum.dfy)). A
  monomial such as `2 * s` inside a polynomial is not matched against the
  definition `s == e` of the context.
- A comparison pattern `b < x` with `b` open does not match `k < x + n`,
  where `b` would be the difference `k - n`, while `0 < x + c` matches with
  `c := n - k` (see
  [benchmark04_conjunctive.dfy](examples/sv-comp/loop-zilu/benchmark04_conjunctive.dfy)).
- A higher-order pattern as a summand, e.g. `G(k)` in `G(k) + b[k]`, matches
  a single summand of the expression, not several, e.g. not `2 * k + 3` in
  `b[k] + 2 * k + 3`, and a variable as the coefficient of a monomial does not
  match a literal coefficient, such that affine updates are not matched
  generically (see [sqm.dfy](examples/sv-comp/array-fpi/sqm.dfy)).
- Rules on a comparison do not match its negation, e.g. a rule for
  `0 <= e` does not apply to `e < 0` (on `Int`, `e + 1 <= 0`), such that
  lemmas are stated in both forms.
- Hypotheses are not split into cases: `X == (if c then A else B)` and
  disjunctions among the hypotheses remain, `-split` followed by another
  `-simplify` splits them (see
  [diamond_1-1.dfy](examples/sv-comp/loop-acceleration/diamond_1-1.dfy),
  [half.dfy](examples/sv-comp/loop-new/half.dfy)).
- Linear facts over more than two variables are not combined: the context
  `n0 <= 0`, `n1 <= 0`, `0 < n0 + n1` is not found inconsistent, since
  `n0 + n1` is no difference constraint (`Diffs`), while `FourierMotzkin`
  would decide it (see [seq-3.dfy](examples/sv-comp/loop-invgen/seq-3.dfy)).
- Expressions with binders are compared literally, not modulo the names of
  their bound variables: `count(0, maps(for ⌊K⌋, ⌊L⌋ yield k₁₀, l₈ :: k₁₀ % 2))`
  and the same with `k, h`, which the right-hand side of a rule introduces,
  are not found equal (see [sumt2.dfy](examples/sv-comp/loops-crafted-1/sumt2.dfy)).
- No integer rounding: `2 * n <= 2 * k + 1` does not give `n <= k`; no
  cancellation of a factor, e.g. `k * j < 1000000 * k`, and a lemma
  `if 0 <= k then (k * a < k * b) <==> (0 < k && a < b)` does not match it,
  since a variable of a pattern does not match the coefficient 1000000 of the
  monomial `1000000 * k` (see [count_by_k.dfy](examples/sv-comp/loop-new/count_by_k.dfy)).

## Trace equation systems (`-teq`)

- The functions on traces are declared only by the lemma database
  ([teq.dfy](resources/cuvee/teq.dfy)), whose names may clash with the input,
  and which inputs cannot use before `-teq` injects it.
- The guards of the updates of traces are the branch conditions of the body
  only; the loop test and assumptions in the body are recorded in `invs`
  (`TEQ.loop`), which the simplifier and the matching assume in the update of
  `X == trace(...)` (`Simplify.invariants` with `self`), but not for traces
  that are not the right-hand side of such an equation.
- The guarded cases of an expression are matched in their order, each against
  some case of the pattern, such that a higher-order guard bound by a later
  case of the pattern is still open when an earlier case of the expression
  needs it.
- Facts about terms are not derived (see [forward.md](forward.md));
  binary_search_partition.dfy needs a cut, `assert φ; assume φ;`, and `-teq`
  does not assume assertions.
- The simplifier knows nothing about division, e.g. `l <= (h + l) / 2` for
  `l <= h` is a lemma in binary_search_partition.dfy.
- Solutions of arithmetic equations are inlined into polynomials only
  (`Chains.solved`), not substituted elsewhere, e.g. `forall x. x == y + 1
  ==> p(x)` stays; a solution that depends on its variable through the
  equations of the context is not inlined (`Chains.acyclic`).
- Higher-order patterns (`Rewrite`) take distinct bound variables or terms
  instantiated already as arguments; other arguments match only if an
  earlier occurrence instantiated the variable, and a single bound variable
  of the pattern cannot abstract several of the expression (no tuples).
  Terms are abstracted at all of their occurrences.
- The prelude teq.dfy is injected after parsing, hence Dafny files with
  lemmas about `counter`, `current`, `earlier`, `count`, ... repeat their
  declarations, also with `-teq`.
- No instantiation of the iteration constraint at a witness, e.g. a search
  whose constraint states that `P` holds before the exit `n`, and `!P(j)`,
  which gives `n <= j`; the examples abstract the constraint by an atom first,
  e.g. `absent(n, a, e)`, which a second lemma takes as its side condition (see
  [standard_sentinel-2.dfy](examples/sv-comp/array-examples/standard_sentinel-2.dfy)),
  since a side condition that is an iteration constraint does not terminate;
  a forward rule on branch `forward` would instantiate it directly.
- teq.dfy has no rule for the length of the iterations of a counter,
  `|⌊counter(i, c, n)⌋| == n` (see [sumt2.dfy](examples/sv-comp/loops-crafted-1/sumt2.dfy)).
- Nested loops: the outer trace takes the values of summarized inner traces,
  whose composition, e.g. `k == n * m`, is not accelerated (see
  [nested-1.dfy](examples/sv-comp/loop-new/nested-1.dfy)).

## Dafny frontend

- Containers: missing comprehensions, `multiset(s)`, the multiset update
  `m[x := n]`, `>=` and `>`, disjointness `!!`, `seq(n, f)`, and
  multi-dimensional updates.
- `x.f` and `x.C?` on variables only; members inside `type`/`datatype` bodies
  need `this.` ([examples/datastructures/stack.dfy](examples/datastructures/stack.dfy)). The
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
  5. tests: [stack.dfy](examples/datastructures/stack.dfy) without `this.`, nested
     accesses `f(x).g()`, errors for unknown receivers.
- `var` declarations before statements; contract clauses in the fixed order
  `modifies`, `requires`, `ensures`, `assumes`, `commits`, `decreases`, for
  loops `modifies`, `invariant`, `decreases`.
- `t.0.1` is scanned as `t` `.` `0.1`.
- The printer's `any` raises `MatchError` on plain strings and numbers.
- Names that are neither identifiers nor operators, e.g. the instances
  `f<Int>` of `-monomorph`, are escaped by backticks, which the scanner reads
  back but Dafny does not have; names containing backticks are not handled.
- Dafny printed from C input (`-print dfy`) is not parsed back: the prelude
  declares a function named `const` with type parameters,
  `function {:c} {:smt2} const<a₀, a₁>(x₀: a₁): array<a₀, a₁>`.
- Parse errors of `fuse` show the term in the internal syntax of the parser
  (`Inner(App(...))`).

## Boogie frontend

- Procedures must be declared before calls (no mutual recursion); no
  `forall<a>`, sequences, or parallel composition.
- Datatypes (`data`, not Boogie) have no testers and no `match`; `data`,
  `and`, and `|` are keywords.
- z3 answers `unknown` for Horn clauses over recursive datatypes
  ([examples/boogie/vcgen/data.bpl](examples/boogie/vcgen/data.bpl)).
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
  ([examples/c/vcgen/div.c](examples/c/vcgen/div.c)), and for calls in loops whose
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
  "goal does not hold" for [bitvectors.dfy](examples/dafny/language/bitvectors.dfy)
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
