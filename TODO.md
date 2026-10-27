# TODO

Open problems, limitations, and planned work; bugs are in [bugs.md](bugs.md). Names such as `sumt2` are SV-COMP
tasks.

## Work queue: database and engine

Priority: more correct results, `true` first; speed only where a task times out that would succeed. Changed
benchmarks are not rerun with Cuvée.

### Now (chosen Oct 27, 2026)

In this order; each is checked on its tasks first, then by one cloud run of Arrays and Loops (no task lost). Open
tasks are from the cloud runs of Oct 27 and 28 (0.52.14 to 0.52.16, Ryzen, 120 s, one core).

- [ ] **Strided stores** (array-tiling, 22 of 29 open: `pr2`-`pr5`, `mbpr2`-`mbpr5`, `pnr2`-`pnr5`, `nr2`-`nr5`,
      `tcpy`, ...). Three gaps, in this order:
      1. done (0.52.15): the parity of successors, `(p + c) % m` from a known `p % m` for `m <= 4`, the case split on
         `p % m` (pr2, mbpr2-mbpr4);
      2. done (0.52.15): the definition of div and mod in the simplex (tcpy, diff-2-n-u); no forward lemmas for
         division;
      3. the 2^s cases of s conditional stores: shape lemmas per number of cases (strides.dfy, Oct 28), pr3 and pnr2
         proved; pr4 at the limit of 120 s (88 s locally), pr5 in 485 s (within the 15 min of the competition);
         pnr3-pnr5 open. Merging the cases was
         rejected by decision, the generic lemma over the window is too general (ideas/conditional-stores.md);
      4. open: nr2-nr5, whose inner loop over two positions leaves cases that store at `2 * k` and `2 * k + 1`, the
         iteration variable written as the literal it equals in each case (ideas/engine-gaps.md, gap 3); no evaluation
         of concrete traces, by decision.
- [ ] **Equalities from the simplex to the classes** (ideas/prove-next.md, section 1): two counts known equal only
      by inequalities stay different terms (`n₂ == SIZE == n₃` by the exit test and the bound of the iteration
      constraint). The general exchange of all equalities lost 21 results of Arrays and 13 of Loops; instead, the
      equation `i == N` at the exit of a loop whose counter the test bounds, stated once per loop, or on demand where
      two atoms of the same function differ only in counts. The zero_sum tasks are solved by `-teq` now (18 of 18);
      measure on zero_sum1 with `-slice`, standard_maxInArray_ground and standard_minInArray_ground-2, then look for
      the tasks of Arrays and Loops whose remaining goal compares such terms. Oct 27: the three are solved (0.52.14),
      and a search of the remaining goals of the cloud logs found no task of this kind; set aside until one shows up.
- [ ] **array-patterns** (37 tasks, 30 true, none solved: 20 unknown, 17 timeouts): a loop `while(1)` stores at a
      nondeterministic index into two arrays (`array1[index] = f(index)`, `array2[index] = g(index)` or kept), and a
      final loop sums both arrays, bounded by a closed form. Plan: the goals after `-teq -prove` of array1 and
      array10 first; then the value of a cell after stores at a list of keys (`if occurs(k, keys) then ... else
      a0[k]`, teq.dfy), a pointwise bound of the sum of both arrays per cell (the cancelling pairs), and a bound of
      a sum by a pointwise bound over a counter; lemmas local to the tasks first, into the database once two tasks
      share them; why 17 time out. Oct 27: the goal of array1 is the sum over a range of two arrays after stores at
      repeating keys, related pointwise (`array2[N - 1 - j] == -array1[j]`); the updates of sums of selects
      (`sum_selects_update`, restored in 0.52.16) decide the last iteration; multisets do not give the rest (the
      relation is pointwise, and the last write per key has no closed form); set aside by decision.
- [ ] **Reducer commutativity** (reducercommutativity 28, array-crafted bAnd, bor, xor 15): the module `teq:multisets`
      (ideas/multisets.md), optional; converting the folds of all lists proves the sums and averages but lost 34 tasks
      (innermost rewriting preempts the rules around the folds); in progress (Oct 28): the twins of the lemmas of
      teq:aggregation on the folds of multisets, which keep the conversion of all folds from preempting them; open:
      sep (a count by a predicate of C's signed `%`), the bitwise reductions (no folds), the Lean model of multisets.
- [ ] functions_1-2 (false, lost in 0.52.16): `forall Result?: List<int> :: length(Result?) != 134217728` needs that a
      list of a given length exists, which neither the rules nor z3 decide. A predicate `haslength(n, xs)` that the
      engine drops when `xs` occurs nowhere else was considered and dropped by decision (Oct 28): one task, and a
      special case of the engine for one function of the database.
- [ ] Report the bugs of sv-benchmarks (bugs.md): the verdict of SV-LIB in-de20, the out-of-bounds read of
      standard_vararg_ground.
- [ ] SV-LIB: the new conventions of sv-benchmarks (`upto` and other tags).
- [ ] Tasks lost since 0.52.4 (ideas/prove-next.md, A2, the table of Oct 28): brs2-brs5
      (`select_current_trace_reset_add_keep`) and ps2-ps6 valuebound1 (`square_eq_self`, the case split on
      two-element intervals) recovered in 0.52.17, pr3 by its shape; open: mods, modsf, functions_1-2, and those at
      the limit.
- [ ] Regressions since 0.51.4 (ideas/prove-next.md, plan A, with a table per task): rewnifrev, linear_sea.ch, geo1,
      prodbin, cohendiv-ll, max20-1 (array_2-*-simple and theatreSquare work again, Oct 26). Few rewrite steps; the
      profile in plan A (side conditions of rules, hashes of terms, the simplex, `Context.fix`) suggests speedups are
      likely not worthwhile; repeated reads of counters (rewnifrev) and unsigned arithmetic with division (linear_sea.ch,
      geo1, prodbin) are relevant for the database. More time (15 min) and its 116 tasks at the step bound:
      ideas/prove-next.md, plan A.
      Experiments of Oct 26, 2026: the portfolio (ideas/portfolio.md), -slice alone (ideas/slice.md).
- [ ] ps2-ll_unwindbound1 times out at 60 s.
- [ ] Recurrences in arrays: `ifcomp` (`c[j] == j^3`, a sum of squares with exact division by 6 as a forward lemma),
      `pcomp`, `sqm-if`, `nsqm-if`, `condm`.
- [ ] Counterexamples by concrete evaluation of `sum`, `map`, `counter` for a literal `n` (30 unsafe array-fpi tasks,
      e.g. brs2f).
- [ ] Lost tasks: in-de52, in-de62 (more loops than the depth of the case splits).
- [ ] partial_mod_count_* (true): conditional stores whose second value is not a constant, then a count of zeros.
- [ ] Arrays (ideas/array-lemmas.md, Oct 26): the gaps of the engine behind the workarounds in the database
      (compactions and filters, copies from both ends, cases split at a position), each listed with its tasks; then
      replace the workarounds by their plain forms; plan in ideas/engine-gaps.md (division and parity: "Now").
- [ ] Deferred: the cost of `-prove` (forward instances are simplified at every firing; a memo of them was measured
      and costs more, Oct 27, so the remedy is fewer forward lemmas: rules on the atoms of the goals); the rest of nla-digbench (geo1,
      geo3, cohencu); the non-terminations at the bound on the steps (fermat1, egcd2, mannadiv); equalities from the
      simplex to the classes (ideas/prove-next.md).
- [ ] Last: integrate the results into doc/paper/cuvee.tex (`scripts/paper.py`), `scripts/out/experiments.pdf`,
      ideas/experiments.md, doc/array-algorithms; commit all the work, then a single push.

## General

- Verify trace lemmas in Dafny; performance of the simplifier; thread `Config` through more code; error messages
  with a printer instead of the internal syntax (also the parse errors of `fuse`).
- SV-COMP: the archive of 0.50.18 is on Zenodo (10.5281/zenodo.23607469), fm-tools passes `-svcomp -fallback -z3
  -timeout 900000` (branch `cuvee-0.50.18` of gernst/fm-tools, the merge request is open); the DOI of doc/paper is
  still that of an earlier archive; keep `cuvee.py` in sync with sosy-lab/benchexec#1327.
- Witnesses with invariants ([ideas/witnesses.md](ideas/witnesses.md)): `-slice` attaches the trace equation systems of
  loops as invariants over the program variables; open: lowering the traces and `invs` that simplification
  keeps (e.g. a trace whose update is a constant, `invs` of a loop with `break`), printing them as `annotate-tag`
  commands of SV-LIB and as `loop_invariant` entries of C witnesses, and checking them with `-vcgen`; violation
  witnesses with the values of a counterexample.
- Simplification of procedures (`Slice`, doc/prove.md, "Programs"): writing back by arithmetic, e.g. `x0 + 2` as
  `x + 1` when `x` holds `x0 + 1`; `Ode` and `Par` are not simplified, attributes are kept as they are.
- SV-LIB: unstructured control flow (labels, gotos), `define-procs-rec`, tags on other statements, `:recurring`,
  `:not-recurring`, `:decreases-lex`, `get-witness`, `select-trace`, answers to `verify-call` for interactive use;
  `-chc` with constants in procedure bodies (Horn solvers reject free constants).
- Lambdas of function type printed in SMT-LIB (arrays) are not read back.
- `-monomorph` leaves polymorphic assertions uninstantiated, which solvers reject.
- Implementations ([ideas/implement.md](ideas/implement.md)): the start of the counter of `renc` (`tick := 0` by
  hand in examples/dafny/renc).
- The implementations of overloaded operators that cvc5 lacks (`seq.store`, `seq.member`, `seq.proper_prefixof`,
  `set.proper_subset`, `set.update`, `bag.select`, `bag.proper_subbag`, `map.store`) are declared but not defined; define them
  in terms of cvc5's functions (then `examples/dafny/vcgen/seq.dfy` and the cvc5 tests of sets).
- Refuted goals are reported in SMT-LIB, not in the language of the input, and without the annotation that failed.
- `Match`: parsed in Dafny expressions only, printed without case conditions, not reduced on constructors.
- Sequences could be axiomatized inductively, as datatypes, instead of the solvers' theory, whose quantified
  specifications end in `unknown` (`positive` in examples/dafny/hybrid/par.dfy).

## Proofs of teq.dfy in Lean

- The index premises of `lean/premises.txt` as `requires` of the lemmas, if `-prove` decides them (only
  documented, by decision).
- `cut` and the predicates of sorted.dfy fix one meaning of functions the engines use through their lemmas only.
- A Lean mode of the printer instead of the text manipulation of `generate.py`; `generate.py` writes an unused
  `open Nat (zero succ)`.
- `simp only` instead of `simp` (the check takes about 20 s); a preamble for `-print lean` (`open Classical`,
  Mathlib, a namespace against clashes such as `List` and `max`).

## Code structure

Cleanup, none of it a bug.

- Core:
  - One generic traversal with binders for `Subst.apply`, `Old.instance`, `Type.expand`, `Rec.calls`.
  - Int and Real twins (`Fun`, `Builtin`, `Overload`, rings); `Ring` without `lt`, `le`, `div`.
  - Four builders of applications (`Overload.app`, `App.apply`, `State.exprs.app`, `smtlib.Parser.app`).
  - Sugar copies (`Sugar.empty`, the arities of `unary`/`binary`/`ternary`, the `all` lists of `Fun`).
  - `Rule.from` could use `Rec.from`; `Fuse.fuse` should keep `hf` and rename its cases (its `Rec` has the
    request's variables as formals).
  - `Subst.apply(attrs)` does not rename `modifies` lists.
  - `State`: one generic table instead of one map per kind; `history` looked up by name instead of `State.history`.
  - `Type`: `unify` and `bind` repeat the unfolding; the error report of `unify` occurs ten times.
  - The ordering of expressions is by `toString`; `Justify` is mapped to its keyword in four places.
- The engine of `-prove`: `(config, state, ctx)` threaded everywhere (→ a class); the matchers of `Rewrite` take
  12 to 15 parameters (→ a matcher per rule); three matchers on types, two on patterns; `Subst.rename` with
  `ctx.bind` ten times (→ `Context.enter`); the matcher's signed summands beside `Poly` (kept on purpose, see
  ideas/engine-consolidation.md, step 2); sequent decomposition three times (`Split`, `Normalize`,
  `Context.assume`, kept by decision, step 8).
- Transforms: abstractness from two sources (`VCGen.abstracts`, the solver's closure in the order of the stream,
  which misses mutual recursion; mark the functions in the `State` instead); `VCGen`, `TEQ`, `Horn` repeat the
  setup of a procedure and pass the four exits separately; `Monomorph` replays the prefix on every flush.
- Frontends: Dafny and Boogie share most syntax, resolvers and grammars; Dafny contracts are fields, Boogie's a
  list of clauses; four folds of collection literals; the `par` and monomorphic forms of SMT-LIB printed separately;
  `c.Parser` (1743 lines) mixes concerns; the flex scanners throw `RuntimeException`.
- Printers and pipeline: the mixfix printers of Dafny, Boogie and C share most methods (→ a base trait);
  recomputed guards (`case _ if f(e).isDefined`); repeated Dafny printer cases; `Pipe.run` handles errors twice and
  lets `StackOverflowError` escape; `-help` lists options in arbitrary order; global mutable state (fresh-name
  counters, printer widths, `Debug.modules`); `object Debug` and `trait Debug` share a name.
- Tests: helpers defined in several suites; two harnesses (`test.Examples`, `test.Expected`); no direct tests of
  easyparse and `prove/Arith`; 444 feature warnings (`String => Name`), 2 deprecations, a non-exhaustive match in
  `prove/Simplify`.

## Matching and rewriting (`-prove`)

- Products are not matched modulo commutativity (`m * k` against `k * m`).
- A lemma that defines a predicate by an iteration constraint with a general body matches the bound of every loop
  (diamond_1-1); such definitions stay local to the tasks.
- `maps_counter_affine` does not match `N + -k + -1`; a map with an unused further dependency matches no lemma on
  maps of the counter (array_init_both_ends_multiple_sum).
- Guards below combinators are matched syntactically first, so a guard variable may match its negation; more
  specific lemmas must come first.
- Variables only in side conditions are instantiated from the facts in the order of the conjuncts, the first match
  is taken; open comparisons are not searched.
- An integer equation as a lemma is a rule on its left-hand side as a term, not on the atom; a monomial `2 * s`
  inside a polynomial is not matched against `s == e` of the context.
- `b < x` with `b` open does not match `k < x + n` (benchmark04_conjunctive).
- A higher-order pattern as a summand takes one summand only, a variable coefficient no literal one (sqm).
- Rules on a comparison do not match its negation; lemmas are stated in both forms.
- Expressions with binders are compared literally, not modulo bound names (sumt2), nor modulo the definitions of the
  context (mapsum1).
- The branches of a conditional formula are not simplified under the facts of the context
  (standard_password_ground).
- Reads over writes at another position are decided without the facts (`Simplify.select`), so `j != 3` does not
  reduce `a[3 := w][j]` (single_elem_safe).
- Conditionals inside equations and products are not lifted (motivex).
- A pattern sum of a rule variable and a bound variable matches only if the variable takes one summand
  (array_tiling_tcpy); a lemma for a monomial with a coefficient does not match it inside an equation (ps2-ll).
- Conjunctions are matched in order, not modulo commutativity (seq-3).
- No integer rounding (`2 * n <= 2 * k + 1` to `n <= k`), no cancellation of factors (count_by_k).
- The matcher has no case for quantifiers, so an existential postcondition needs a witness (max_element).
- Only variables have definitions in the matcher: a term matched by a member of its class that contains it cycles.
- Closed conditions with binders are looked up modulo classes and renaming, not modulo arithmetic or unused
  dependencies.
- A side condition that contains a trace as a term gets fresh bound variables at every evaluation, so its views are
  never memoized (insertion sorts, first_duplicate).
- A bound variable defined by an arithmetic equation is not eliminated (`y == x + 1`), nor a bound variable equal to
  a free one when it is the canonical member of the class (binders.smt2, normalize.smt2 of examples/smtlib/prove).
- Performance: the simplex is rebuilt at every check that is not cached (an incremental tableau per context); the
  step budget of 1000 per command is reported as non-termination; the negation of an integer equation asks for both
  bounds; guard decisions are repeated without a cache; `Rewrite.conditions` simplifies conjuncts before
  instantiation; equations are matched in both orders; every round of `Simplify.apply` simplifies the whole formula
  again (standard_copy9_ground); non-termination is found only by the budget or a stack overflow after 8 to 13 s.

## Trace equation systems (`-teq`)

- The algorithms: max_element (no quantified left-hand sides), cocktail_sort and counting_sort (step budget) are
  open (doc/array-algorithms).
- The read relation of the partition takes the guards for every result, so a counter with equal cases joins the
  cycle that the guards read.
- `-fallback`: lists of traces of several accumulators have no test.
- The functions on traces are declared by teq.dfy only, whose names may clash with the input.
- The guards of updates are the branch conditions only; the loop test is assumed only for traces that are the
  right-hand side of an equation.
- Guarded cases are matched in order, so a higher-order guard bound by a later case is still open for an earlier one.
- Which lemmas of the database should be `{:fw}` rather than `{:rw}`.
- Division in the arithmetic of `-prove` only by the definition of `t div k` and `t mod k` for a literal `k`
  (0.52.15), not for `quot` of C, no cancellation (`2 * n / 2`, mlceu2).
- The selection of dependencies is not backtracked when a side condition fails (nested_mult).
- A bare bound variable in the body of an `invs` pattern is synthesized as a map and matches every fragment of that
  shape (cocktail_sort, selection_sort); `Rule.check` could reject such left-hand sides with `invs` side conditions.
- A bound that is not a difference constraint is not decided from two facts (cocktail_sort).
- A polymorphic lemma with a higher-order variable of the type parameter's type in a side condition is not matched.
- Literal disjunctive guards, store indices and initial values in trace patterns are matched only through a
  higher-order variable pinned by a quantified side condition (merge, insertion_sort, cocktail_sort).
- A higher-order variable for an array read is instantiated by the array itself (prefix_sums).
- A variable argument of an uninterpreted function is not expanded by its definition when a pattern is matched
  below it; a pattern sum of two variables is not matched (merge).
- A closed side condition equating a list with a trace fails, since `⌊I⌋` is not expanded (merge, counting_sort).
- A quantified hypothesis is matched by no side condition (counting_sort states it as an atom).
- Arithmetic premises of a quantified side condition are substituted before the step lemmas see them
  (insertion_sort2).
- Higher-order patterns take distinct bound variables or instantiated terms, no tuples.
- No instantiation of the iteration constraint at a witness (standard_sentinel-2).
- The composition of summarized inner loops (`k == n * m`) is not accelerated (nested-1).
- The grammars of Dafny and Boogie need a comma after the last initial value of a trace before `for`.
- `-teq` is exponential in sequences of conditionals and overflows at ten (bugs.md; conditional stores in
  [ideas/conditional-stores.md](ideas/conditional-stores.md)).

## Dafny frontend

- Containers: comprehensions, `multiset(s)`, the multiset update, `>=` and `>`, `!!`, `seq(n, f)`,
  multi-dimensional updates.
- `x.f` and `x.C?` on variables only. Plan: testers on terms by the constructor; functions and selectors on terms by
  a generic member application resolved after type checking (`Overload`); method calls on terms last; tests with
  examples/datastructures/stack.dfy without `this.`.
- Names escaped by backticks (instances of `-monomorph`) are not Dafny; names containing backticks are not handled.

## Boogie frontend

- Procedures declared before calls (no mutual recursion); no `forall<a>`, sequences, parallel composition.
- `data`: no testers, no `match`.
- z3 answers `unknown` for Horn clauses over recursive datatypes (examples/boogie/vcgen/data.bpl).
- The printer rejects other loop attributes, binders, derivatives, ODEs, `par`, and prints `goal`, `lemma`,
  `decreases`, `continue`, which are not Boogie.

## C frontend

- Signed overflow is not modelled; unsigned loop counters (`x = uint(x + 1)`) are no counters for `-teq`.
- `goto` to a label whose statement falls through (26 tasks, mostly backward gotos of the reducers, which could be
  loops).
- No structs (37 tasks end in a generic parse error, not "not supported"), unions, bitwise operators of integers,
  preprocessor, `&`, `*p`, pointer arithmetic, arrays of pointers, GCC builtins. Floating point numbers are
  uninterpreted (`c.Parser.floats`): properties of the floats themselves (freire1/2) are not proved, `long double` is
  not parsed; the aiob/ofuf tasks of loop-industry-pattern fail on comma expressions with string literals.
- Array parameters that a function assigns as in/out parameters (arrays are values; wrong false verdicts, bugs.md).
- z3 answers `unknown` for Horn clauses with division by variables (div.c) and for calls in loops whose callee has
  no goals.
- ACSL: `\min`, `\max`, `\abs`; labels of `\at` other than `Pre`, `Here`, `LoopEntry`; contracts of functions that
  read globals need their values as preconditions; interpret `shl`, `shr`, `bitand`, ... where possible
  (`(x & 5) == 5` as `x % 8 == 5`); `-chc` answers `unknown` on unsigned arithmetic of annotated programs.
- ACSL on SV-COMP ([benchmarks/acsl](benchmarks/acsl); Oct 23, 0.50.2, 60 s, `-split` only for `Loops-split.set`:
  288 of 320 true tasks of Arrays, 467 of 555 of Loops): why z3 fails on the parts of `-split` (35 tasks prove only
  without it); `prodbin-ll` and `prod4br-ll_valuebound5` prove only with it (2 to 3 s) and belong in
  `Loops-split.set`; `copy-partial-3-u` has weak annotations (refuted at 15 min, a timeout at 60 s), the other
  `copy-partial-*`, `add-*`, `diff-*` time out; annotate the VerifyThis tasks; nonlinear closed forms (`geo*`,
  `lcm2`, `prod4br`, `partial_mod_count_2-5`, `array26`).

## SV-COMP

- A portfolio in Cuvée: `-teq` for a short slice, then `-chc`, then `-fallback`, in sequence (BenchExec counts the
  CPU time of all cores), parsing shared; disagreement is `unknown`.
- Task definitions: the properties and expected verdicts are read but not used; a single input file only.

## Bitvectors

- No simplifier rules; widths cannot be parameters.
- Dafny: no `<<`, `>>`, infix `|`, `RotateLeft/Right`, `bv0`; `x as int < n` needs parentheses.
- Boogie: types `bv8`, literals `5bv8`, `++`, extraction, `{:bvbuiltin}` functions.

## Parallel composition

- `Horn` rejects `parallel` and ignores assumptions and commitments; only calls can be composed.
