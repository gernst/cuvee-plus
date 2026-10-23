# Bugs

Wrong results, errors, crashes, and non-termination, as of 0.46.7 (Oct 13, 2026), and the bugs found in the
benchmarks of others (sv-benchmarks); limitations and planned work are
in [TODO.md](TODO.md). Soundness comes first: a wrong proof costs more than any open goal (SV-COMP: -32 for a wrong
true, -16 for a wrong false).

## Soundness

### Open

- **A bound variable captures a constant of the same name** (confirmed with 0.46.7, `-prove` and the former `-simplify`):
  `(declare-const x Int) (declare-const y Int)` with the goal `(=> (exists ((x Int)) (< x y)) (<= x y))`, which
  is not valid (`x = y + 1`), is turned into the valid `(forall ((x Int)) (=> (< x y) (<= x y)))`, so a solver
  after `-prove` proves it. Normalization renames bound variables apart from the free variables,
  but constants are functions and are not avoided. The Dafny examples of `-teq` bind their variables with
  `forall` (CLAUDE.md), which avoids it there; SMT-LIB and Boogie inputs with constants are exposed (formerly an
  entry of TODO.md, whose example this is).

- **`sat` of `-chc` with uninterpreted bit operations** (moved from the portfolio in TODO.md): the prelude declares the bit operations
  (`bitand`, `bitor`, `bitxor`, `bitnot`, `shl`, `shr`) without definitions,
  so Z3 may choose their interpretation in clauses that use them and report
  them satisfiable for a program that is not safe; `sat` should count only
  if the clauses use no such function, which Cuvée can check.
  Still open in 0.48.0: `Horn.report` takes `sat` of the clauses for `correct`
  ([Horn.scala](src/cuvee/verify/Horn.scala), `checked`), even if the clauses apply a function declared
  `:abstract`; the fix of 0.42.1 covers refuted goals only (`Solver.sink`). `Cmd.funs` of the clauses against
  the abstract functions, as for goals, would make it `unknown`.

- **Parallel composition** (`-hybrid`, moved from TODO.md):
  - Sequential calls neither establish the callee's assumption nor guarantee
    its commitment (unsound); commitments are checked only at `send`/`receive`/`tick`
    directly in the body.
  - The results of `send`, `receive`, and `tick` must be assigned to the global
    `history`, which is not checked.

### Trusted without a check

What the engine assumes and nothing checks: each item is a gap between the rules and the semantics, harmless in
the contexts that `-teq` builds, as far as the reasons go.

- **Dependencies of equal length** (formerly a section of TODO.md):

  The combinators assume that their dependencies have equal lengths (an invariant of the core, see
  `Type.dependencies`), which teq.dfy never states: e.g. `current_stores` holds only if `|keys| == |values|`, and
  `current_trace_flag` only if `|hs| == n` for the dependency `⌊counter(0, 1, n)⌋`. In Lean, the dependencies are
  zipped, which truncates to the shortest one, so such lemmas are false without the assumption.

  Plan:

  1. Make the invariant part of the semantics: a term is well-formed if the dependencies of each combinator in it,
     also in the definitions of the functions of teq.dfy (`stores(a, keys, values)` is a trace over `keys, values`),
     have equal lengths. The lemma database is sound for well-formed terms only, which is all that -teq builds: the
     dependencies of a loop are `⌊X⌋` of its traces, which all have `n` steps.
  2. Rewriting preserves the invariant if each lemma maps well-formed left-hand sides to well-formed right-hand
     sides, e.g. `prefix_stores` cuts `keys` and `values` to the same length. This is a proof obligation of each
     lemma, not a check at run time.
  3. In Lean, each lemma gets the hypotheses that the combinators of its left-hand side are well-formed:
     `d₁.length = d₂.length` for the dependencies, with the lengths of `butlast (counter i c n)` and of the other
     functions given by lemmas (the length of `butlast (counter ...)`, of `maps` and of `butlast (trace ...)`),
     stated by hand in lean/TEQ/Proofs.lean; a lemma about the right-hand side (well-formedness) is proved along with it.
  4. Lemmas whose assumptions cannot be derived from well-formedness (`earlier_consts` outside the trace,
     `prefix_prefix` for `j > k`) get `requires`, which makes them conditional rules; check on the SV-COMP
     database that the simplifier still discharges them in the contexts of the goals.
  5. Document the invariant and the soundness of the database modulo it in doc/teq.md.
- The premises that the engine does not check are listed in [lean/premises.txt](lean/premises.txt): nine reads and
  prefixes within the loop and two lengths. Open: turn the index premises into `requires` where `-prove` decides them
  in the contexts of the goals (item 4 above), measured on the tests and the SV-COMP rows, which would shrink the
  list to the soundness gaps proper.
- The guards of `case` updates are printed as `if g₁ then e₁ else if g₂ then e₂ else unspecified` since 0.46.11, so
  their completeness is an obligation of the proofs; the lemmas with arbitrary guards end in a case for the
  complement of the others since Oct 14, 2026 (doc/teq.md). Their disjointness is still assumed: overlapping guards
  take the first case, a refinement of the choice of the core.
- **Lemmas without a proof**: none in [lean/open.txt](lean/open.txt); the module
  `nested`, which has no Lean proofs; the abstract predicates of the examples (`sorted`, `perm`, `partitioned`,
  `bubbled`, `shaken`, `argmin`, `insert`, `shake`, `nodup`, `merged`, `lb`), axiomatized by their lemmas, and the
  summary lemmas of examples/dafny/algorithms, which state the correctness of an inner loop in one line
  (doc/array-algorithms/principles.tex, Soundness; doc/teq.md); ACSL lemmas, which are
  `:free`, and lemmas with `:free` in general (`Solver` assumes them like axioms).
- **`-fallback` does not assume the premises above** (equal lengths, indices within the lists, complete guards);
  doc/teq.md names this a candidate cause of its wrong proofs (see below).

### Fixed, to be confirmed

- The bisection of `teq:search` was inconsistent (found by the Lean proofs, Oct 13, 2026): the rule `bisection`
  guarded both cases by `lo < hi`, a step after the exit was `unspecified`, and `bisection_lo` bounded it, which gave
  `unspecified.0 == l0` for every `l0` (for `l0 == h0`, one step, `G` and `H` false). Fixed on Oct 14, 2026:
  `bisection` is a definition with `{:fold}` in place of the rule, with disjoint guards (the second case excludes
  `G`) and a third case that keeps the state, so the bounds hold for every run and are proved in Lean (doc/teq.md,
  complete guards). The three examples (`bsearch_bisect`, now `algorithms/bsearch.dfy`, `bsearch_safe`, removed on
  Oct 23, 2026, and `lower_bound`) close. A version with `G`
  alone (`H` as `¬G`) loses the bound `hi >= upper` of the searches with a third branch, since `hi` would move onto
  occurrences of the key.

- `-fallback -z3` proves `nla-digbench-scaling/fermat1-ll_unwindbound{1,2,5,10,20,50,100}` of SV-COMP (expected
  unsafe: the shared counter `counter++ < N` of the three nested loops exits them early, after which the final
  assertion fails), after about 340 s each, in the 15-minute runs of `xml/cuvee-full-fallback.xml` of Oct 11, 2026
  (0.36.3, without `-unbounded`); the runs of Oct 10 with 60 s and 120 s stopped them at `TIMEOUT (true)`, so not
  new; `-teq` without the fallback leaves them unknown, `-chc` (1 min) times out. Fixed in 0.42.2: `TEQ.loop` told
  the exits of a loop apart by assumptions (`¬test`, the test before a `break`), while an enclosing loop guards the
  cases of its updates by the branch conditions of the paths only, such that the normal exit (here infeasible,
  `while (true)`) and the `break` exits overlapped, `case true => c case φ => c + 1`, whose lowering contradicts
  itself for φ; the exits are branch conditions now (`examples/c/verify/teq_nested_break.c`,
  `fermat1-ll_unwindbound1` is `unknown`, 627 s). Still wrong in the 15-minute runs of 0.42.1 (5 of them, the
  others time out); a rerun with 0.42.2 is pending, which may also lose correct results that came from such
  contradictions.
- `-fallback -z3` proves `benchmarks/sv-comp/dafny/nla-digbench/geo1-u` (expected unsafe), in the runs of
  `xml/cuvee-quick-fallback.xml` of 2026-10-10 15:25 and 16:12: a soundness problem of the encoding or of the
  lemmas it relies on, not yet analysed; possibly the overlapping exits of loops above (fixed in 0.42.2), to
  check. Its C version is unsafe only by the wrap-around of `unsigned long long`,
  which the C frontend models without `-unbounded` (0.36.0): the fallback no longer proves geo1-u and its 14
  variants in nla-digbench-scaling, Z3 finds a model instead (15-minute runs of Oct 11, 2026), and `-chc` reports
  the violation; with `-unbounded`, it proves it again, as the semantics drops the wrap-around. The Dafny version,
  over mathematical integers, has not been rerun.
- **The published SV-COMP archive** (0.41.4, 10.5281/zenodo.23317707) predates the entry points (25c90e96):
  `-teq` checks functions out of the context of their calls and answers `incorrect` for `sanfoundry_24-1` and
  `verifythis/lcp` (wrong false). Fixed in the code; the archive is wrong until a new version is published (see
  the SV-COMP tool entry in TODO.md).
- **Vacuous proofs of the examples** (examples/dafny/algorithms/NOTES.md, finding 13; `pending/first_duplicate`):
  the entry below. Neither case reproduces with 0.46.7 (Oct 13, 2026): `fd2_d3.dfy` prepended to
  `program_wrong.dfy` and `program2_wrong.dfy` (with `-include` of `aggregation`, `arrays`, `search`,
  `counters`, which the migration requires) leaves a goal under `-teq -simplify` and `-teq -prove`, and `vac.dfy`
  leaves both of its goals. The mechanism is not excluded by design: `Rewrite.conditions` simplifies an instance
  of a side condition in `ctx.neutral`, which keeps the facts of the goal, in both engines; `Context.active`
  suspends only the rule itself. A harness that runs each `-teq` example with its `*_wrong` variant
  would catch a recurrence.
- A side condition that is an `invs` is matched in the context of the fact's combinator, where other rules fire,
  also with the hypotheses of the goal: in [first_duplicate.dfy](examples/dafny/algorithms/first_duplicate.dfy) a rule
  `nodup(a, k, n) <==> true` under the hypothesis `distincts(...)` rewrote the condition
  `invs(for ⌊counter(0, 1, m)⌋, rs check k, r :: r == !nodup(a, k, n))` of a lemma on `distincts(...)` into the fact
  `invs(... :: !r)`, so that `distincts(...)` was proved from itself, also for the negated postcondition; the path
  through the split goals is not isolated. Side conditions of a rule should not be simplifiable by rules that use
  the conclusion; atoms as side conditions (`agree_prefix` style) avoid it.

### Deviations of the semantics, by decision

Not bugs, but they decide verdicts; the details are in TODO.md (C frontend).

- C: signed overflow is not modelled; `-unbounded` also drops the wrap-around of unsigned integers (which proves
  `geo1-u`, unsafe only by it); arrays are values, so the updates of a callee to an array parameter do not reach
  the caller (the ACSL tasks that relied on it take their arrays as global variables since Oct 14, 2026); variables declared without a value are
  arbitrary integers; memory safety is not checked (`\valid` is true).
- `-vcgen`: without a measure, termination is not checked (`VCGen.scala:99`).

## Errors and crashes

- C: variables named like the constants of SMT-LIB, `int true = 1; int false = 0;`
  (`benchmarks/acsl/loops-crafted-1/watermelon`), keep their names and reach z3 as `(true Int)`, a sort error
  ("solver error"); such names need renaming in the frontend.
- `-teq` overflows the stack (an uncaught `StackOverflowError` in `Subst`) on
  a loop body with ten conditionals in sequence, presumably from the 2^10
  paths of its symbolic execution (see
  [diamond_2-2.dfy](benchmarks/sv-comp/dafny/loop-acceleration/diamond_2-2.dfy)).
- A solver error stops the run with the error instead of an answer, e.g. `-teq -prove -z3` without
  `-fallback` (`unknown constant integer (Nat)`); an error of the solver could count as `unknown` for its goal
- An input file with an unknown extension, e.g. a preprocessed C file
  `.i`, ends in an uncaught exception with a stack trace
  ("unsupported command line option or input file"), since `Config.parse`
  raises outside of the pipeline; the task definitions (`.yml`) of such
  files are read.
- Readers of input files and the stream of `-o` are never closed.
- The stderr of a solver is never read, which can block it.
- `t.0.1` is scanned as `t` `.` `0.1`.
- The printer's `any` raises `MatchError` on plain strings and numbers.
- Dafny printed from C input (`-print dfy`) is not parsed back: the prelude
  declares a function named `const` with type parameters,
  `function {:c} {:smt2} const<a₀, a₁>(x₀: a₁): array<a₀, a₁>`.

## Non-termination and timeouts

- **`-prove` is slower than the former `-simplify` on polynomial loops** (Oct 13, 2026, 0.46.5 to 0.46.9, measured locally and on
  the cloud at 60 s): nla-digbench-scaling/bresenham-ll_valuebound1 takes 8 s with teq.dfy alone, 11 s with
  `teq:arithmetic` and `teq:unsigned`, 46 s with `teq:aggregation` in addition (the other modules add 0 to 4 s); of
  that, about 20 s are the three forward lemmas of aggregation (`count_nonnegative`, `current_maxs_initial`,
  `current_mins_initial`), the rest its rewrite rules. A profile (15 samples) has 6 of 15 in `Forward.saturate` and
  `fire` (the instances are matched and simplified again at every assumed fact, without a memo, see
  ideas/prove-next.md) and 12 of 15 in `Rewrite.matches`. The matcher changes of 0.46.5 are not the cause (46 s
  before, 41 s after). On SV-COMP Loops at 60 s, `xml/cuvee-fallback.xml` lost 63 tasks against 0.42.1 (`-simplify`,
  Oct 12, i9-9900), 38 of them in nla-digbench-scaling, mostly timeouts (bresenham-ll_valuebound1 38 s before, 68 s
  now, almost all of it in `-prove`): 196 true, 20 false against 233, 28. The same without `-fallback` gained.
- **Forward instances use up the steps of a goal** (0.46.3 on): `natural_positive` and `store_occurs_selects` are
  instantiated and simplified again wherever they fire, which uses up the 1000 steps of the goal on array-crafted
  bAnd*, bor*, xor*, reducercommutativity avg*, sum*, data_structures_set_multi_proc_ground-2 ("rewriting does not
  terminate" instead of `unknown`, no correct result lost). Steps of their own for each instance (0.46.8) turned the
  breaks into timeouts and were reverted (ideas/prove-next.md).

- A rule whose left-hand side is a comparison of two open variables, e.g.
  `j < n` with a side condition `invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: P(k, h))`,
  overflows the stack before any step: it matches every comparison, also
  the bounds `0 <= k < n` of the iterations that matching the `invs` of the
  side condition assumes in the context of its body (`Simplify.combinator`),
  where the rule is tried again (see
  [standard_find_ground-1.dfy](benchmarks/sv-comp/dafny/array-examples/standard_find_ground-1.dfy)).
- A pattern with two cases matches an update with a single case, which one
  case of the pattern covers (`Rewrite.matchesUpdates`); variables of the rule
  that occur only in the other case stay uninstantiated, and the rule is
  applied anyway: the lemma
  `trace(x0, ... :: case c => F(x, k, h) case !c => G(x, k, h)) == if c then trace(... F ...) else trace(... G ...)`
  rewrites `trace(a, ... :: x[h := x[h] + 2])` to
  `if true then trace(... F ...) else trace(... G ...)` with `G` free, which
  does not terminate (see [condm.dfy](benchmarks/sv-comp/dafny/array-fpi/condm.dfy)).
  This is why the joins of guarded stores are not part of teq.dfy: they
  match every store with one case, e.g. `a[k := a[-k + 99999]]` of
  [standard_palindrome_ground.dfy](benchmarks/sv-comp/dafny/array-examples/standard_palindrome_ground.dfy),
  as `if true then ... else G(a, k, h)` with `G` free, which hides the update
  from other lemmas.
- A cycle through the arithmetic: in [ss1.dfy](benchmarks/sv-comp/dafny/array-fpi/ss1.dfy), the equation
  `sum₄₀ == sum₂₂ + sum(selects(a₃₁, ⌊I₃₉⌋))` is solved for `sum₂₂` (`Chains`), whose value is then inlined into
  `⌊consts(n, sum₂₂ + 1)⌋`, which `selects_stores` returns for `selects(a₃₁, ⌊I₃₉⌋)`, which reappears in the
  solution; the poly guard against cycles (`Simplify.poly`) sees the equations of the context only, not the rules.
  Remedies: prefer to solve for the variable that occurs in fewer definitions (`sum₄₀`), or reject a rewrite whose
  result contains the rewritten term (`Rewrite.apply`). Also non-terminating, not analysed yet:
  [add-3-n-u](benchmarks/sv-comp/dafny/array-multidimensional/add-3-n-u.dfy), `copy-partial-3-u`, `diff-3-n-u`.
- A cycle through a side condition that is an iteration constraint, resolved for `sum_invs_const` of teq.dfy, which
  was `consts_prefix_def` and `sum_consts_prefix` (in legacy/teq.dfy since Oct 23, 2026, replaced by `consts_choice` and `sum_consts`), with the atom `consts_prefix(n, c, js)` abstracting the
  constraint like `agree_prefix`; the mechanism remains for any rule with a general left-hand side and an `invs` side
  condition: `sum_invs_const` had the left-hand side `sum(js)`, which matches every sum, and the side condition
  `invs(for ⌊counter(0, 1, n)⌋, js check k, j :: j == c)`, open in `n` and `c`, which `Rewrite.conditions`
  simplifies and then matches against the facts. Matching it against an `invs` fact (`Rewrite.matches`) builds the
  simplifier's context of that fact's combinator (`Simplify.combinator`), whose reads of the dependencies
  (`Simplify.iterations`) are rewritten, e.g. `earlier(natural(k), ⌊X⌋)` to `sum(prefix(natural(k), ...))` by
  `earlier_sums`, on which `sum_invs_const` is tried again, with the same fact, one level deeper, until the budget is
  exhausted (the cache of `Context.combinators` is filled only after the context is complete); e.g.
  [ps2-ll.dfy](benchmarks/sv-comp/dafny/nla-digbench/ps2-ll.dfy) repeats the same eight steps 122 times, 30 s, and
  terminates after 48 steps without the lemma; likewise ps3-ll to ps6-ll, cohencu-ll, cohendiv-ll, for_bounded_loop1,
  copy-3-n-u, diff-2-n-u (13 of the 16 errors of the Dafny translations at 0.34.22). Such a rule is not decreasing
  in the sense of conditional rewriting (its condition is not smaller than its left-hand side), which `Rule.check`
  could reject statically: no `invs` in a side condition whose dependencies are variables of the left-hand side.
  The decisive ingredient is the second one, a left-hand side that matches what the rewriting of the reads
  produces: the fragment lemmas of [fragments.dfy](examples/dafny/algorithms/fragments.dfy) have `invs` side conditions
  over the lists of their left-hand sides, but their left-hand sides are `invs` fragments with specific bodies, and
  they terminate in every file; `invs_subst_counter` (body `t == F(k, J)`, higher-order) and `earlier_invs_def`
  (left-hand side `earlier(natural(i), ts)`) of the first version of
  [row_sums.dfy](examples/dafny/algorithms/row_sums.dfy) cycle. A side condition on the current value of the trace
  that the rule rewrites, `current(Hv) <= current(Lv)` for a left-hand side `current(trace(...))`
  ([lower_bound.dfy](examples/dafny/algorithms/lower_bound.dfy)), is the same re-entrance through the decision of a
  closed condition instead of the search; remedy 1 covers both.
  Remedies in the engine (1 done in 0.42.3, with two more that the traces of the cycles showed to be needed:
  the reads of a combinator context are normalized by the rules without an `invs` condition only, since a chain of
  different rules with `invs` conditions nests through the contexts of the facts they are matched against, and the
  reads are cached by the dependencies and the definitions of the traces, since the contexts of a fact are rebuilt
  at every position at which a condition is matched against it; the six cycles of `pending/` and of this entry
  terminate, none of them closes its goal, see doc/prove.md):
  1. A reentrance guard for conditional rules: while the side condition of a rule is decided, the rule is not
     applied inside, e.g. a set of such rules in the context that `Rewrite.apply` skips; this cuts the recursion
     for all conditional rules, and loses only side conditions that need the same rule again.
  2. Open side conditions that contain combinators are only substituted, not simplified, before they are searched
     among the facts, which are simplified already; simplification is needed for normalization elsewhere, e.g.
     beta reduction after a higher-order match, hence only for combinators.
  3. A separate budget for side conditions, whose exhaustion leaves the condition undecided, such that the rule
     does not apply instead of aborting the command: a safety net, which turns errors into open goals.

  Not remedies, measured on the Dafny translations: stating the lemma as the definition
  `invs(... j == c) <==> js == ⌊consts(n, c)⌋` rewrites the `invs` facts that `Simplify.invariants` uses
  pointwise; recording the counters that the context iterates over and not injecting their invariants again
  (`Context.iterating`) ends bresenham-ll only; not renaming the bound variables of combinators, with binders
  that shadow those of the context (`Context.bind` hiding the facts about them), makes the terms stable across
  rounds, but the repetitions above remain, and it closes nothing (241 against 243 true, within the noise).
  The injection of 7b420a0, all invariants over the counter of a loop pointwise with `earlier(natural(k), Z)`, made
  the nested reads recurse further (19 errors), and is reverted in 0.34.23.
- [sanfoundry_02_ground.dfy](benchmarks/sv-comp/dafny/array-examples/sanfoundry_02_ground.dfy) times out (60 s), on the trace
  of the two largest elements, whose updates read the array at the counter from 2.

## Matching failures

Rules that should apply and do not; recorded as bugs, unlike the limitations of the matcher in TODO.md.

- A side condition that is an equation between applications with a variable
  that is not instantiated yet, e.g. `prefix(n, xs) == prefix(n, ys)` with `n`
  open, is not matched against an equal hypothesis
  `prefix(N, t) == prefix(N, u)`, while `q(prefix(n, xs), prefix(n, ys))` and
  `xs == ys` are; reproduced with the former `-simplify` alone on a lemma
  `if prefix(n, xs) == prefix(n, ys) then (earlier(j, xs) == earlier(j, ys)) <==> true`
  (see [standard_compare_ground.dfy](benchmarks/sv-comp/dafny/array-examples/standard_compare_ground.dfy),
  which uses the predicate `agree` instead).
- A sum that contains a bound variable of a combinator in a pattern is not
  matched, even against the same sum: the lemma
  `current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[k := a[k + -1]])) == hit(a0)`
  does not rewrite `current(trace(a2, for ⌊counter(0, 1, N)⌋ do a, k :: a[k := a[k + -1]]))`
  with the former `-simplify`, while `a[k := a[k] + d]` matches `a[k := a[k] + 6]`;
  recurrences over the previous element are not matched (see
  [ifcomp.dfy](benchmarks/sv-comp/dafny/array-fpi/ifcomp.dfy)), only those whose
  index is a dependency, e.g. `⌊counter(1, 1, n)⌋` (see
  [eqn1.dfy](benchmarks/sv-comp/dafny/array-fpi/eqn1.dfy)).
- Rule variables are not renamed apart from the free variables of the goal: if the goal has a variable `Ns` and
  a lemma's side condition has its own variable `Ns`, the open condition coincides with the fact literally, is
  decided true without binding `Ns`, and `Rewrite.apply` reports "variables of a rule not instantiated by its
  match", which replaces the goal; a pin `forall lo, hi :: G(lo, hi) <==> a[(hi + lo) / 2] < x` with the lemma's `x`
  unbound was decided only because the method's variable is also named `x` (see
  [fragments.dfy](examples/dafny/algorithms/fragments.dfy), whose test methods name their sequences `KK, NN, ...` apart,
  and [lower_bound.dfy](examples/dafny/algorithms/lower_bound.dfy)).
- A left-hand side `current(trace(0, for ⌊counter(0, 1, nn)⌋, hs do ...))` matched against `current(Lo)` through the
  definition `Lo == trace(...)` of the trace variable in the context binds the higher-order guard but leaves the
  dependency variables `nn` and `hs` unbound: a rule then fires with "variables of a rule not instantiated by its
  match", or its identifying equations `nn2 == nn` stay open and are never matched (the probes of lower_bound.dfy,
  NOTES.md finding 32).
- A lemma of an injected module (`-include teq:nested`) does not fire on a goal where the identical lemma, included
  as a user file or written in the input, does: `invs_counter_consts` of nested.dfy on
  [row_sums.dfy](examples/dafny/algorithms/row_sums.dfy) (`-rules` does not list it; it fires on transpose.dfy, and
  the two further chain lemmas stay in row_sums.dfy for this reason, NOTES.md finding 34). Not understood: the rules
  differ by the attribute `{:teq}` and by their position among the rules.
- The exit of a loop in the conclusion of a goal is a disjunction, `i < n && !r || r == !distincts(...)` for the exit
  `!(i < n && !r)`, which `-split` does not split, and the context of the second disjunct does not contain the literals
  of the negated first, so a rule on the atom of the postcondition sees neither `n <= i` nor `r`; a case split on the
  negated exit when it is a disjunction would make a postcondition stated as an equivalence work
  ([first_duplicate.dfy](examples/dafny/algorithms/first_duplicate.dfy) states it as two implications instead).
- An instantiated higher-order variable leaves a beta-redex in the output, `((k: int) => !nodup(a, k, n))(k)`
  (first_duplicate.dfy with a lemma `current(results(x0, ks, maps(for ks yield k :: F(k))))`).

## Flaky tests

- Tests that run z3 have its default timeout of 1 s per query, which a
  loaded machine may exceed: `c.Translation.increments in expressions` failed
  with `unknown` while z3 unrolled a loop with the constant bound 10 (about
  0.17 s alone); with a symbolic bound it finds a linear invariant (0.035 s).
- Return to the bitvectors of Dafny: the test suites over
  `examples/dafny/vcgen` (`SimplifyPrograms`, `VCGen`, `Split`) reported
  "goal does not hold" for [bitvectors.dfy](examples/dafny/language/bitvectors.dfy)
  sometimes in the full test run, depending on the tests run before it in the
  same JVM; alone, and with `java -jar cuvee.jar -vcgen -z3`, it
  passes. The fresh-name counters are reset per run (`Cuvee.pipe`), so some
  other state persists across runs. The example is moved out of `vcgen`,
  hence no suite runs it.

## Bugs of sv-benchmarks

Tasks of [sv-benchmarks](https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks) whose expected verdict is wrong or
whose program is not well defined, found on Oct 14, 2026 (sv-benchmarks at 4d6b7c1d7ce). Not reported yet.

- **`sv-lib/c-translated/loops-crafted-1/in-de20`: expected `false`, but the check holds.** The verdict was flipped
  from correct to incorrect in c2d3abfeb ("Fix verdict of task whose behavior depends on a bounded data type"), but
  this task does not depend on the bound. Over `Int`, `x := n; y := 0`, the first loop moves `x` to `y`, `z := y`,
  the second moves it back, and the check `x == n` holds for every `n`: for `n <= 0` both loops are skipped. Proved by
  Cuvée (TEQ), and by z3 on the inductive invariants `x + y == n`, `y >= 0`, `x >= 0` if `n > 0`, `x == n && y == 0`
  otherwise (first loop), `x == n - z`, `z >= 0` (second loop). The C original (unsigned) is expected true. All three
  participants of SV-COMP 2026 time out on it. Our result files of Oct 14 take it as expected true (patched,
  originals in `results/*.orig`).
- **`c/array-examples/standard_vararg_ground`: an out-of-bounds read in a task expected true.** `while (aa[a] >= 0)
  a++;` reads up to the first negative element of the nondeterministic array `aa[100000]`, beyond the array if
  there is none, which is undefined behavior in C; the verdicts `unreach-call` true and `termination` true assume
  that the read stops within the array. Verifiers that check memory safety refute it: TriCera answered false on our
  translation (benchmarks/sv-comp/c), which assumes a negative last element since (`aa[N - 1] < 0`, keeping the
  verdict true; README there). Our Dafny translation (benchmarks/sv-comp/dafny) reads an unbounded map, where a read
  beyond `N` is an arbitrary value, not undefined: its verdict true holds (the loop may not terminate, which
  `unreach-call` allows); SV-LIB has no translation of it.

## Fixed

- **`verify-call` of SV-LIB assumed the precondition of the called procedure instead of checking it** (Oct 14, 2026,
  the run of CoreVerification): `loop-add.1` calls `add (x0 y0)` without `(assert (<= 0 y0))`, `add` has
  `:requires (<= 0 y0)`, the task is expected false, and both `-teq` and `-chc` answered true. Fixed in 0.46.14: a
  verify-call mimics a call in the global SMT context, so the precondition must follow from the declarations and
  axioms for the arguments; `TEQ.precondition` adds that goal, `Horn.entry` a query clause. Locally `-chc` answers
  false on `loop-add.1`, `-teq` unknown (sound; the counterexample search does not take the constant `y0` as a
  variable); `loop-add.2` stays true. Confirmed locally with the jar of 0.46.14 (Oct 14), and the result files of the
  cloud runs of 0.46.13 patched accordingly (`results/*.orig` are the originals); confirmed on the cloud by the run of
  `xml/cuvee-fallback.xml` on 0.46.14 (loop-add.1 correct false). The other five tasks there end in
  errors of the frontend (`unknown tag "upto"`), since sv-benchmarks merged new SV-LIB conventions.

- A rule is applied while the instances of its own side conditions are simplified (`Rewrite.conditions` simplifies an
  instance before it decides or matches it): a condition that mentions the term of the rule's left-hand side, e.g.
  `l == current(Lv)` for a rule on `current(Lv)` with `Lv` bound, does not terminate
  ([lower_bound.dfy](examples/dafny/algorithms/lower_bound.dfy), whose sound ties of the exit to the traces all
  fail this way; the summary of bubble_sort.dfy takes `current(results(...))` as left-hand side instead of `results(...)`
  for the same reason). The rule should be disabled, or the instance not rewritten, while its conditions are evaluated.
  Done: the rule is suspended while its left-hand side is matched and its conditions are evaluated
  (`Context.active`, `Rewrite.applyActive` in both engines).
- SV-LIB (0.39.0), wrong verdicts on `sv-benchmarks/sv-lib/core-verification` (property correct-tags), found with
  the run definition `SV-LIB_correct-tags` of `xml/cuvee-chc.xml` and `xml/cuvee.xml` before running them:
  - `-chc -z3` refutes `loop-add` (expected true): the clauses of `verify-call add (x0 y0)` contain the goal
    `forall y0. 0 <= y0`, the precondition of `add` over all values of the constants, which fails; the task
    expects the precondition of the called procedure to be assumed (`-teq` proves the task).
    Done in 0.39.4: `verify-call` assumes the precondition for the arguments (`Horn.entry`; `VCGen` emits no
    goal for it), `loop-add` is true with `-chc -z3`. Consequence: `loop-add-incorrect-invariant` (expected false
    by its `:not-recurring`, the invariant itself holds) was refuted by the precondition goal before, by accident.
    Resolved by sv-benchmarks d1b5aaf48f9, which renamed `:not-live` to `:not-recurring`: `svlib.Parser.properties`
    rejects `:recurring` and `:not-recurring` as not supported, so the task (and the 8 others with
    `:not-recurring`) ends in an error instead of a wrong verdict, until the properties are supported.
