# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## New

- `-verify` (see [ideas/verify-answers.md](ideas/verify-answers.md)): a refutation is classified per goal, `VCGen`
  marks the whole goal of a procedure `:abstract` if one of its loops has no invariant, also the obligations that do
  not depend on that loop, which `-split` keeps apart
- `-verify` stops at a solver error with the error instead of an answer, e.g. `-teq -simplify -z3 -verify` without
  `-fallback` (`unknown constant integer (Nat)`); an error of the solver could count as `unknown` for its goal
- support verifying trace lemmas in Dafny
- identify performance improvements, notably in the simplifier
- thread config through more code, so that it is usually available
- error messages should use a nice printer
- C frontend: `goto` to a label whose statement falls through, by copying
  the statements
- witness output: SV-COMP scores verdicts without a validated witness with 0
  (doc/paper/README.md); correctness witnesses need loop invariants (from
  the models of Z3 for `-chc`, or derived from the trace equation systems),
  violation witnesses a path (from the counterexamples of `-chc`); see
  "Portfolio of TEQ and CHC" below
- SV-LIB: the frontend (`cuvee.svlib`, see doc/architecture.md) lacks
  unstructured control flow (labels and gotos, e.g. by a loop over a program
  counter, with the invariants of labels as `pc = k ⇒ φ`), `define-procs-rec`,
  tags on statements other than loops, procedure bodies and sequences (0.39.0:
  `(! (sequence ...) :tag t)` is a `core.Block` with attributes, whose
  `check-true` annotations `State.annotated` asserts at its beginning, as the
  translated C tasks of SV-COMP use for their assertions; the printers of C,
  Boogie and Dafny drop the attributes of blocks, and the SMT-LIB printer
  writes them as `(! (sequence ...) ...)` of SV-LIB, which the SMT-LIB parser
  does not read, by decision), the liveness
  properties `:recurring` and `:not-recurring`, which 6 of the 7 core
  verification tasks use, and `:decreases-lex`, `get-witness` (the query
  `GetWitness`, answered `unsupported`; see witness output) and
  `select-trace`, the answers `correct`/`incorrect` to
  `verify-call` for interactive use (the verdict is decided by cuvee.py),
  constants in the bodies of procedures with `-chc` (Horn solvers reject free
  constants, the entry clause quantifies only those of the arguments and
  axioms); a dangling tag is an error, the report says to ignore it
- SV-COMP tool entry and zenodo archive: the archive of 0.41.4 is published
  (10.5281/zenodo.23317707, in fm-tools `data/cuvee.yml`, merge request !1176,
  and in doc/paper); it predates the entry points (25c90e96), without which
  `-teq` checks functions out of the context of their calls
  (`sanfoundry_24-1`, `verifythis/lcp` answered `incorrect`): package and
  upload a new version (`scripts/zenodo.py package`, `upload`, published by
  hand) and enter its DOI in fm-tools and doc/paper. The experiments of the
  paper loaded all modules of the database (`-include teq:nested`, `sorting`,
  `strides`), the options in fm-tools do not: align them. The tool-info module
  `cuvee.py` is the pull request sosy-lab/benchexec#1327 (branch `add-cuvee`
  of github.com/gernst/benchexec), to be kept in sync with this repository
- a portfolio of `-teq` and `-chc` within the time limit, see "Portfolio of
  TEQ and CHC" below

## Bugs

- C: variables named like the constants of SMT-LIB, `int true = 1; int false = 0;`
  (`benchmarks/acsl/loops-crafted-1/watermelon`), keep their names and reach z3 as `(true Int)`, a sort error
  ("solver error"); such names need renaming in the frontend.
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
- `-fallback -z3` proves `nla-digbench-scaling/fermat1-ll_unwindbound{1,2,5,10,20,50,100}` of SV-COMP (expected
  unsafe: the shared counter `counter++ < N` of the three nested loops exits them early, after which the final
  assertion fails), after about 340 s each, in the 15-minute runs of `xml/cuvee-full-fallback.xml` of Oct 11, 2026
  (0.36.3, without `-unbounded`); the runs of Oct 10 with 60 s and 120 s stopped them at `TIMEOUT (true)`, so not
  new; `-teq` without the fallback leaves them unknown, `-chc` (1 min) times out. Presumably the lowering for Z3
  loses a constraint of the early exits, as for geo1-u below; not yet analysed.
- `-fallback -z3` proves `benchmarks/sv-comp/dafny/nla-digbench/geo1-u` (expected unsafe), in the runs of
  `xml/cuvee-quick-fallback.xml` of 2026-10-10 15:25 and 16:12: a soundness problem of the encoding or of the
  lemmas it relies on, not yet analysed. Its C version is unsafe only by the wrap-around of `unsigned long long`,
  which the C frontend models without `-unbounded` (0.36.0): the fallback no longer proves geo1-u and its 14
  variants in nla-digbench-scaling, Z3 finds a model instead (15-minute runs of Oct 11, 2026), and `-chc` reports
  the violation; with `-unbounded`, it proves it again, as the semantics drops the wrap-around. The Dafny version,
  over mathematical integers, has not been rerun.
- A bound variable may capture a constant of the same name in the output of
  SMT-LIB: normalization renames bound variables apart from free variables,
  but constants (`declare-const x`) are functions, e.g.
  `(=> (exists ((x Int)) (< x y)) (<= x y))` becomes
  `(forall ((x Int)) (=> (< x y) (<= x y)))` with `-simplify`.
- A rule whose left-hand side is a comparison of two open variables, e.g.
  `j < n` with a side condition `invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: P(k, h))`,
  overflows the stack before any step: it matches every comparison, also
  the bounds `0 <= k < n` of the iterations that matching the `invs` of the
  side condition assumes in the context of its body (`Simplify.combinator`),
  where the rule is tried again (see
  [standard_find_ground-1.dfy](benchmarks/sv-comp/dafny/array-examples/standard_find_ground-1.dfy)).
- A side condition that is an equation between applications with a variable
  that is not instantiated yet, e.g. `prefix(n, xs) == prefix(n, ys)` with `n`
  open, is not matched against an equal hypothesis
  `prefix(N, t) == prefix(N, u)`, while `q(prefix(n, xs), prefix(n, ys))` and
  `xs == ys` are; reproduced with `-simplify` alone on a lemma
  `if prefix(n, xs) == prefix(n, ys) then (earlier(j, xs) == earlier(j, ys)) <==> true`
  (see [standard_compare_ground.dfy](benchmarks/sv-comp/dafny/array-examples/standard_compare_ground.dfy),
  which uses the predicate `agree` instead).
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
- A sum that contains a bound variable of a combinator in a pattern is not
  matched, even against the same sum: the lemma
  `current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[k := a[k + -1]])) == hit(a0)`
  does not rewrite `current(trace(a2, for ⌊counter(0, 1, N)⌋ do a, k :: a[k := a[k + -1]]))`
  with `-simplify`, while `a[k := a[k] + d]` matches `a[k := a[k] + 6]`;
  recurrences over the previous element are not matched (see
  [ifcomp.dfy](benchmarks/sv-comp/dafny/array-fpi/ifcomp.dfy)), only those whose
  index is a dependency, e.g. `⌊counter(1, 1, n)⌋` (see
  [eqn1.dfy](benchmarks/sv-comp/dafny/array-fpi/eqn1.dfy)).
- A cycle through the arithmetic: in [ss1.dfy](benchmarks/sv-comp/dafny/array-fpi/ss1.dfy), the equation
  `sum₄₀ == sum₂₂ + sum(selects(a₃₁, ⌊I₃₉⌋))` is solved for `sum₂₂` (`Chains`), whose value is then inlined into
  `⌊consts(n, sum₂₂ + 1)⌋`, which `selects_stores` returns for `selects(a₃₁, ⌊I₃₉⌋)`, which reappears in the
  solution; the poly guard against cycles (`Simplify.poly`) sees the equations of the context only, not the rules.
  Remedies: prefer to solve for the variable that occurs in fewer definitions (`sum₄₀`), or reject a rewrite whose
  result contains the rewritten term (`Rewrite.apply`). Also non-terminating, not analysed yet:
  [add-3-n-u](benchmarks/sv-comp/dafny/array-multidimensional/add-3-n-u.dfy), `copy-partial-3-u`, `diff-3-n-u`.
- Rule variables are not renamed apart from the free variables of the goal: if the goal has a variable `Ns` and
  a lemma's side condition has its own variable `Ns`, the open condition coincides with the fact literally, is
  decided true without binding `Ns`, and `Rewrite.apply` reports "variables of a rule not instantiated by its
  match", which replaces the goal; a pin `forall lo, hi :: G(lo, hi) <==> a[(hi + lo) / 2] < x` with the lemma's `x`
  unbound was decided only because the method's variable is also named `x` (see
  [fragments.dfy](examples/dafny/algorithms/fragments.dfy), whose test methods name their sequences `KK, NN, ...` apart,
  and [lower_bound.dfy](examples/dafny/algorithms/lower_bound.dfy)).
- A rule is applied while the instances of its own side conditions are simplified (`Rewrite.conditions` simplifies an
  instance before it decides or matches it): a condition that mentions the term of the rule's left-hand side, e.g.
  `l == current(Lv)` for a rule on `current(Lv)` with `Lv` bound, does not terminate
  ([lower_bound.dfy](examples/dafny/algorithms/lower_bound.dfy), whose sound ties of the exit to the traces all
  fail this way; the summary of bubble_sort.dfy takes `current(results(...))` as left-hand side instead of `results(...)`
  for the same reason). The rule should be disabled, or the instance not rewritten, while its conditions are evaluated.
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
- A side condition that is an `invs` is matched in the context of the fact's combinator, where other rules fire,
  also with the hypotheses of the goal: in [first_duplicate.dfy](examples/dafny/algorithms/first_duplicate.dfy) a rule
  `nodup(a, k, n) <==> true` under the hypothesis `distincts(...)` rewrote the condition
  `invs(for ⌊counter(0, 1, m)⌋, rs check k, r :: r == !nodup(a, k, n))` of a lemma on `distincts(...)` into the fact
  `invs(... :: !r)`, so that `distincts(...)` was proved from itself, also for the negated postcondition; the path
  through the split goals is not isolated. Side conditions of a rule should not be simplifiable by rules that use
  the conclusion; atoms as side conditions (`consts_prefix` style) avoid it.
- A closed side condition that is an `invs` over variables bound by earlier conditions is decided by the simplifier, which
  does not find it among the facts (these keep unused dependencies, e.g. the traces of `lo` and `hi`, and their bound
  variables are renamed), so the condition fails although the fact exists; the condition must be written over fresh
  variables, matched, and identified by equations (`js6 == js4 && Js6 == Js3`). This was the condition of
  [cocktail_sort.dfy](examples/dafny/algorithms/cocktail_sort.dfy) that blocked its summary for a day (the one
  run that closed the goal presumably decided the closed condition by chance), found with truncated copies of the
  lemma with its first k conditions; the same closed instance also loses its unused dependencies when the simplifier
  simplifies it (`invs(for ⌊Kv⌋, ⌊Rv⌋, ⌊Iv⌋ check k, h, i :: !h)` becomes two dependencies,
  [first_duplicate.dfy](examples/dafny/algorithms/first_duplicate.dfy)). A closed `invs` condition should be matched
  against the facts modulo unused dependencies instead.
- A cycle through a side condition that is an iteration constraint, resolved for `sum_invs_const` of teq.dfy, which
  is `consts_prefix_def` and `sum_consts_prefix` now, with the atom `consts_prefix(n, c, js)` abstracting the
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
  Remedies in the engine:
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
- `-teq` overflows the stack (an uncaught `StackOverflowError` in `Subst`) on
  a loop body with ten conditionals in sequence, presumably from the 2^10
  paths of its symbolic execution (see
  [diamond_2-2.dfy](benchmarks/sv-comp/dafny/loop-acceleration/diamond_2-2.dfy)).

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
- An input file with an unknown extension, e.g. a preprocessed C file
  `.i`, ends in an uncaught exception with a stack trace
  ("unsupported command line option or input file"), since `Config.parse`
  raises outside of the pipeline; the task definitions (`.yml`) of such
  files are read.
- Readers of input files and the stream of `-o` are never closed.
- `Match`: parsed only in Dafny (expressions, without case conditions, not
  statements), printed in Dafny and SMT-LIB without case conditions; the
  simplifier does not reduce it on constructors (only `Fuse` selects cases),
  no rewriting modulo matches.
- Tests that run z3 have its default timeout of 1 s per query, which a
  loaded machine may exceed: `c.Translation.increments in expressions` failed
  with `unknown` while z3 unrolled a loop with the constant bound 10 (about
  0.17 s alone); with a symbolic bound it finds a linear invariant (0.035 s).

## Dependencies of equal length

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
   stated by hand in teq.lean; a lemma about the right-hand side (well-formedness) is proved along with it.
4. Lemmas whose assumptions cannot be derived from well-formedness (`earlier_consts` outside the trace,
   `prefix_prefix` for `j > k`) get `requires`, which makes them conditional rules; check on the SV-COMP
   database that the simplifier still discharges them in the contexts of the goals.
5. Document the invariant and the soundness of the database modulo it in doc/teq.md.

## Proofs of teq.dfy in Lean

- [teq.lean](resources/cuvee/teq.lean) is maintained next to teq.dfy: the statements of new lemmas are printed by
  `./Cuvee.sh -print lean resources/cuvee/teq.dfy` and copied there, with the premises that the printer cannot add
  by hand (see the header of teq.lean). All lemmas are proved, no `sorry` remains; the counterexamples at the end of
  the file show the premises that are needed: dependencies of equal length, indices within the lists, and complete
  guards.
- The Lean check takes about 6 to 9 s, mostly `simp` and typeclass inference for the decidability of `if` on generic
  types under `open Classical`; `simp only` instead of `simp` would speed it up.

## Printers

- The Lean printer (`-print lean`) prints no preamble: the output needs
  `open Classical` and Mathlib (`ℝ`, `Set`), and names of the input that
  Lean declares already clash, e.g. a datatype `List` or a function `max`,
  which a namespace around the output would avoid. Not checked with Lean.
- The C printer of the Dafny translations of SV-COMP
  (`benchmarks/sv-comp/dafny`, `-print c -known dfy,teq,rw`): all 651 print as
  C that parses again (`benchmarks/sv-comp/c`), whose programs, printed back as
  Dafny, are those of their sources. The translations use `quot` and `rem` of
  the prelude of Dafny for the division and remainder of C, have no global
  variables where C would initialize them to zero (`loops/eureka_05`,
  `n.c40`, `nec40`), and fill the constant arrays of C by loops with arbitrary
  values (`loops/vogal-1`, `vogal-2`, `eureka_01-2`).

## Code structure

Opportunities for cleaning up, making the code uniform, and merging common
concepts, found by reading the whole code base; none is a bug.

### Core

- One generic traversal with binders: `Subst.apply`, `Old.instance`,
  `Type.expand(expr)` and `Rec.calls` each repeat the list of binders
  (`Bind`, `Lam`, `Trace`, `Maps`, `Invs`, `Let`, `Match`, `Rec`); the `Match`
  and `Rec` loops of `Old.instance` are the same. `Type.numerals` uses
  `expr.map` for its side effect, which a fold over the children would serve.
  `Type.expand(prog)` repeats the cases of `Prog.map`.
- Numeric sorts: Int and Real are twins in `Fun.int`/`Fun.real`, in
  `Builtin` (`Ints` and `Reals`), in `Overload.int`/`Overload.real`, and in
  their rings `Ints.ring` and `Reals.ring`.
  - `isSum`, `isArith` and `isComparison` enumerate the functions by hand.
  - `Ring` lacks `lt`, `le` and `div`, hence `Simplify.once` (`Eq`, `Lt`, `Le`,
    `Gt`, `Ge`, `not`, `diff`), `Rewrite.comparison`, `Diffs` and the
    printers spell out both sorts.
  - `Ints` and `Reals` are the objects per numeric sort with the sugar,
    literals, and ring; `Ring` could take their comparisons as well.
- Builders of applications: `Overload.app` binds types without expanding,
  `App.apply(state, ...)` expands, `State.exprs.app` instantiates fresh type
  parameters, and `smtlib.Parser.app` does the same again. Two builders with
  clear roles would do.
- Sugar: `Seqs`, `Sets`, `Bags` and `FinMaps.empty` are copies
  (→ `Sugar.empty`). `Sugar.unary/binary/ternary` are one class for three
  arities. `associative` and `commutative` overlap in `flatten`. The `all`
  lists of `Fun.seq`, `set`, ... are written by hand.
- `Rec.from` and `Rule.from(state, fun, body)` both turn a definition that
  matches on a formal into cases. `Rule.from` does not substitute the pattern
  for the formal; it could use `Rec.from`. `Rule.from` accumulates premises
  with `if cond == True then ... else And(...)`.
- `Subst.apply(attrs)` maps expressions only, so `modifies` lists are neither
  renamed nor retyped, while `Type.expand(attrs)` handles them
  (→ `Attrs.map` with a function for variables).
- `State` keeps a declaration, attribute and definition map per kind (sorts,
  functions, variables, procedures). Each repeats the checks "already
  declared" and "not declared" (→ one generic table). `exprs.trace`, `map`
  and `all` repeat the creation of the bound variables.
- `history`: `State.history` exists, but `Prog.Par`, `Type.check(Ode)` and
  `VCGen.tick` look up `state.vars.get("history")`.
- `Type`:
  - `unify` and `bind` repeat the unfolding of defined sorts;
  - `Error.report("type mismatch", ...): unify(...)` occurs about ten times;
  - the checks of `Match` and `Rec` repeat those of the cases;
  - the comment above `BitVec` belongs to `object Param`.
- The ordering of expressions is by `toString` (a TODO in `Expr`).
- `Justify` is mapped to its keyword in four places:
  `smtlib.Parser.justification`, `smtlib.Printer.command`,
  `dafny.Printer.format` and `boogie.Printer.format`.
- `Attrs(attrs.map(_ -> None))` for flag attributes occurs six times in the
  Dafny parser (→ `Attrs.flags`).

### Simplifier

- `Simplify`, `Rewrite` and `Fuse` thread `(config, state, ctx)` through
  every method (→ a class `Simplifier(config, state)`). Programs are
  simplified without context, yet `ctx` is passed.
- The matching functions of `Rewrite` take 12 to 15 parameters.
  - `config`, `state`, `ctx`, `params` and `vars` are fixed per rule; `locals`,
    `self`, `bound` and `avoid` change below combinators
    (→ a matcher object per rule and a record for the binding).
  - The three combinator cases repeat the construction of the inner context.
- Matchers:
  - three on types: `Type.bind`, `Type.unify` and the one-sided
    `Rewrite.matches` on types;
  - two on constructor patterns: `Rewrite` and `Fuse.matches` (`Outcome`).
  - The simplifier does not select the cases of a `Match` on constructors.
- `Subst.rename(bound, ctx.free)` followed by `ctx.bind`/`forall`/`exists`
  and the renaming of the body occurs about ten times
  (→ `Context.enter(bound)`).
- `Simplify.integers`, which turns the bound naturals that occur only as
  `integer(n)` into integers within their range, is clumsy: a filter, a map
  for the new variables, a substitution as a map, and a fold for the
  replacement, with `asInteger` and `integer` as two traversals that collect
  by side effect and rebuild by `Expr.map`; it runs on every quantifier
  before the body is simplified, and the cases `All` and `Ex` repeat the
  wrapping of the ranges (→ one traversal that collects the occurrences and a
  `Subst` for the replacement, or a rewrite of `integer(n)` when entering the
  binder via `Context.enter`, see above).
- The counter of the iterations, `Butlast(ctx.↑(Counter(Zero, One, n)))`, is
  extracted in `Rewrite.iterations`, `Simplify.iterations` and
  `Simplify.deps` (→ one extractor).
- In `Simplify.once`, `Eq(x, Trace(...))` repeats the case `Trace(...)` and
  `Eq(y, Maps(...))` the case `Maps(...)`.
- Polynomials:
  - `Arith.toPoly` and `Simplify.poly` are the same descent;
  - `Rewrite.comparison` recomputes `Simplify.difference`;
  - `Rewrite.signed`, `summands`, `negate` and `sum` belong in `Poly`;
  - `Arith.normalize` is unused.
- Sequent decomposition along the connectives is done three times:
  `Split.assert/assume` (obligations), `Normalize.flatten` (one clause) and
  `Context.assume(pos, neg)` (facts). `Split.avoid` equals `Normalize.avoid`.
- Naming and leftovers:
  - `Context.not` (double negation) and `Simplify.not` (normal form) have the
    same name but different contracts;
  - `Simplify.show(expr)` and `show(rule)` duplicate the one-line rendering;
  - `Rewrite.unmatched` is an alias of `Nil`;
  - commented-out code in `Rewrite.apply`;
  - trailing spaces in `Simplify.arith`.
- `FourierMotzkin` is used only by its test (see below).

### Transforms and verification

- `VCGen`, `TEQ` and `Horn` repeat the setup of a procedure (→ one helper):
  - the contract and the globals `gs` with fresh copies `gs_`;
  - `Old.elim` of the body and the postcondition;
  - the goal `All(in ++ out ++ gs, Imp(pre, ...))`;
  - dropping `DeclareProc`/`DeclareVar`.
- `VCGen.wp` and `Horn.wp` pass the four exits (normal, break, continue,
  return) separately (→ a record). Horn's `decls`/`clauses` and VCGen's
  `gs`/`proc`/`assume`/`commit` are threaded (→ a class per procedure).
- Duplicated helpers:
  - the loop variables `(body.mod ++ attrs.modifies).toList.distinct`
    (`VCGen.loop`, `TEQ.modified`);
  - the fresh measures `Expr.vars("m", ...)` (`VCGen`, `Horn`);
  - the save and restore of shadowed variables (`TEQ` `Block` and `call`).
- `Monomorph` threads `(state, poly, instances, out)` (→ a class per run). Its
  comment refers to `Sink.known`, which is `Sink.knows`. It replays the whole
  prefix on every flush, which is quadratic for long incremental inputs.
  Keeping the instances across flushes needs a transform with state, which
  `Stage` does not provide.
- `Flat` looks up `datatype(state, ...)` repeatedly with
  `Some(...) = ...: @unchecked`.

### Frontends

- The checks of a procedure are written three times:
  `smtlib.Parser.procedure`, Dafny `MethodDef` and Boogie `ProcDef` (→ one
  helper on `State`). Each checks that it modifies only globals, fixes the
  inputs and the unmodified globals, then calls `progs.check`.
- Dafny and Boogie:
  - Syntax: they share most nodes (literals, `App`, `Inner`, `Ite`,
    quantifiers, `Lam`, `Combinator`, `Sel`, `Constr`, the statements, `Lhs`,
    `Axiom`/`Lemma`, the `Syntax` token object).
  - Resolvers: they repeat the datatype declaration, the update
    `a[i][j] := v` (a verbatim copy), the combinator update with `Eps`
    (written twice in each), the assertion with its remaining type parameters,
    `formula`/`measure`, the statements from `Skip` to `While`, and `Ex`/`All`/`Lam`.
  - Grammars: they repeat `translate`/`avoid`/`Sym`, `nil`/`none`/`true_`/`skip`,
    `some`/`list`/`angle`, and the combinator grammar.
  - (→ a shared syntax, or at least shared resolution and grammar traits.)
- Dafny contracts are separate fields (`mod`, `req`, `ens`, `assumes`,
  `commits`, `dec`) in `FunDef`, `MethodDef` (12 fields) and `While`.
  Boogie's are a list of `Spec` clauses, which Dafny could use too. Dafny
  attributes are names only, Boogie's have arguments.
- Dafny `SeqLit`/`SetLit`/`BagLit`/`MapLit` are four folds of "empty, unit,
  join", mirrored by the four recognizers `elems`/`members`/`multiset`/`pairs`
  of the printer (→ one table of collection literals).
- SMT-LIB parser and printer: the polymorphic (`par`) and monomorphic forms
  of `declare-const`, `declare-fun`, `define-fun`, `assert`, `declare-proc`
  and `define-proc` are separate cases with the same body (→ parse and print
  `par` once). `forall` and `exists` are copies.
- `Source.newParser` of Dafny and Boogie are identical up to the package, and
  `c.Source` repeats Boogie's inline. `yml.Source` parses the C prelude twice.
- Subscripts: `boogie.Grammar.index` turns `a₃` into the string `a$3`, which
  the conversion to `Name` parses again. Dafny relies on that conversion
  alone.
- `c.Parser`:
  - `typ` and `zero` repeat the errors for `void` and `float`;
  - the comment on global variables without initializer sits above `array`
    instead of `zero`;
  - at 889 lines, it mixes the resolution of expressions and statements, the
    inference of modifies (`assigned`, `effects`, `calls`, `writes`) and the
    translation unit, which could be split.
- The flex scanners throw `RuntimeException` on unexpected characters
  instead of `Error`.

### Printers and pipeline

- The mixfix printers of Dafny, Boogie and C share many methods
  (→ a base trait with the operator tables and the terminator as parameters):
  - `name`, `commas`, `call`, `str`, `any`, the five `lines`;
  - `doc(Result)`, the control commands, `format`;
  - `params`, `attribute(s)`, `isClause`, `clauses`, `header`;
  - `braces`, `statements`, `block`, `level`, `doc(expr, context)`;
  - `dependencies`, `combinator`.
- Differences between them:
  - Boogie's error strings replace quotes instead of escaping them;
  - its `isClause` lacks `assumes`/`commits`.
- Recomputed guards: the pattern `case _ if f(expr).isDefined => val Some(...)
  = f(expr): @unchecked` (Dafny `elems`, `members`, `multiset`, `pairs`,
  `prefix`, `comparisons`, `infix`, and the same in Boogie and C) computes `f`
  twice (→ extractor objects, as for `bitvector`/`conversion`).
- Repeated printer cases in Dafny:
  - the update `base[index := value]` is printed by five identical cases;
  - the read `base[index]` by four, `|x|` by four;
  - the operator tables of `Sets` and `Bags` are the same list.
- `smtlib.Printer.attr` and the `any` of the mixfix printers both print
  resolved attribute values.
- `pipe.Printer` has four `lines` overloads for lists.
- `Solver.Sink`:
  - `attrs.retain("named", "pattern")` occurs three times;
  - every case returns `(x, Nil, this)`.
- `util.Tool.pipe` returns `(in, out, ...)` from the process's view, which
  `Solver` binds as `(out, in, ...)`. `Tool.run` and `util.Run` are unused.
- `Pipe.run`:
  - it handles `Error` and `NonFatal` twice, inside the loop and around it;
  - a `StackOverflowError` is not `NonFatal` and escapes as a crash (see
    Bugs);
  - `if (!incremental)` is parenthesized.
- `Config`: every transform flag repeats `config.using(X)`. `flags` is an
  unordered map, so `-help` lists the options in arbitrary order. `suffix`
  returns `null`.
- Global mutable state: the fresh-name counters of `Var` and `Param` (reset
  in `Cuvee.pipe` and `test.Expected`), the printer widths set by
  `-linewidth`, including `sexpr.Printer.width` (hence `-linewidth 80` in
  `Expected`), and `Debug.modules` (→ one context per run).
- `object Debug` (debug output) and `trait Debug` (raising errors, implemented
  by `Error` only) share a name. `raise[A]` has an unused type parameter.
- `easyparse/Sugar.scala` has commented-out extensions; `Mixfix` writes
  `if (...)`.
- Remove `src/cuvee/boogie/Scanner.java~`, an editor backup tracked by git,
  and add `*~` to `.gitignore`.

### Tests

- `rw`, `app` and `R` are defined in `simplify/Rewrite`,
  `simplify/RewriteTraces` and `dafny/TEQ`. `Contexts` defines `simplify`
  three times and shorthands such as `v`, `c`, `P`, `lit`.
- `test.Examples` (`output`, `errors`, `stream`) and `cuvee.test.Expected.run`
  are two harnesses that run a command line in memory.
- No direct tests of easyparse (`Mixfix` precedences and associativity,
  `Repeat`, `Intersperse`) and of `simplify/Arith`.
- Warnings of `mill -i compile`:
  - 444 feature warnings (the implicit conversion `String => Name` without
    `-language:implicitConversions`);
  - 2 deprecations;
  - a possibly non-exhaustive match on `Bind` in `Simplify.scala:129`.

## Solvers

- The stderr of a solver is never read, which can block it.
- Axiomatization of data types: sequences are left to the solvers' theory,
  where quantified specifications often end in `unknown` (e.g. `positive` in
  [examples/dafny/hybrid/par.dfy](examples/dafny/hybrid/par.dfy)), whereas inductive
  axioms, as for datatypes, work better; sequences could be axiomatized
  inductively instead.

## Simplifier and rewriting

- A lemma that defines an auxiliary predicate by an iteration constraint with a general body, e.g.
  `invs(... :: x <= b) <==> below_prefix(n, xs, b)`, matches the bound of every loop, `x < N` as `x + 1 <= N`
  (the body generalized to a map), and hides it from the lemmas on traces (`loop-acceleration/diamond_1-1`), hence
  such definitions stay local to the tasks (`loop-invariants/linear-inequality-inv-*`).
- The pattern `a + b * v` of `maps_counter_affine` does not match `N + -k + -1` with `b == -1`, and a map with a
  further dependency that its body does not use matches no lemma on a map of the counter alone, hence the local
  lemmas `occurs_1` and `indexof_1` of `array-cav19/array_init_both_ends_multiple_sum`; general variants of the
  lemma did not help and made `array_init_var_plus_ind2` open.
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
  work (see [gauss_sum.dfy](benchmarks/sv-comp/dafny/loop-new/gauss_sum.dfy)). A
  monomial such as `2 * s` inside a polynomial is not matched against the
  definition `s == e` of the context.
- A comparison pattern `b < x` with `b` open does not match `k < x + n`,
  where `b` would be the difference `k - n`, while `0 < x + c` matches with
  `c := n - k` (see
  [benchmark04_conjunctive.dfy](benchmarks/sv-comp/dafny/loop-zilu/benchmark04_conjunctive.dfy)).
- A higher-order pattern as a summand, e.g. `G(k)` in `G(k) + b[k]`, matches
  a single summand of the expression, not several, e.g. not `2 * k + 3` in
  `b[k] + 2 * k + 3`, and a variable as the coefficient of a monomial does not
  match a literal coefficient, such that affine updates are not matched
  generically (see [sqm.dfy](benchmarks/sv-comp/dafny/array-fpi/sqm.dfy)).
- Rules on a comparison do not match its negation, e.g. a rule for
  `0 <= e` does not apply to `e < 0` (on `Int`, `e + 1 <= 0`), such that
  lemmas are stated in both forms.
- Hypotheses are not split into cases: `X == (if c then A else B)` and
  disjunctions among the hypotheses remain, `-split` followed by another
  `-simplify` splits them (see
  [diamond_1-1.dfy](benchmarks/sv-comp/dafny/loop-acceleration/diamond_1-1.dfy),
  [half.dfy](benchmarks/sv-comp/dafny/loop-new/half.dfy)).
- Linear facts over more than two variables are not combined: the context
  `n0 <= 0`, `n1 <= 0`, `0 < n0 + n1` is not found inconsistent, since
  `n0 + n1` is no difference constraint (`Diffs`), while `FourierMotzkin`
  would decide it (see [seq-3.dfy](benchmarks/sv-comp/dafny/loop-invgen/seq-3.dfy)).
- Expressions with binders are compared literally, not modulo the names of
  their bound variables: `count(0, maps(for ⌊K⌋, ⌊L⌋ yield k₁₀, l₈ :: k₁₀ % 2))`
  and the same with `k, h`, which the right-hand side of a rule introduces,
  are not found equal (see [sumt2.dfy](benchmarks/sv-comp/dafny/loops-crafted-1/sumt2.dfy)).
- Expressions are compared literally, also modulo the definitions of the
  context: `sum(selects(x, ⌊K⌋))` and `sum(selects(x, ⌊counter(0, 1, 100)⌋))`
  with `K == counter(0, 1, 100)` are not found equal, since definitions are
  followed in matching only (`Context.↑`), and a side condition
  `ks == ⌊counter(0, 1, m + 1)⌋` with `ks := ⌊K⌋` is not decided (see
  [mapsum1.dfy](benchmarks/sv-comp/dafny/array-crafted/mapsum1.dfy)).
- The branches of a conditional formula are not simplified under the facts
  of the context: `r != 0 ==> if a then 1 == r else 0 == r` stays, while
  `r != 0 && 0 == r ==> p` is closed; nor is a disjunction among the
  hypotheses, `(a && 1 == r || !a && 0 == r) && r != 0` (see
  [standard_password_ground.dfy](benchmarks/sv-comp/dafny/array-examples/standard_password_ground.dfy)).
- `-split` also splits lemmas marked `{:rw}`, e.g. an equivalence with a
  conditional on its right-hand side, into parts that are no valid rules, on
  which a following `-simplify` fails with "variables of right hand side do
  not occur in left hand side or condition".
- Reads over writes at a different position are decided in the neutral
  context (`Simplify.select` with `ctx.neutral`), without the facts: `j != 3`
  among the hypotheses does not reduce `a[3 := w][j]` to `a[j]`; a lemma
  `if j != i then a[i := v][j] == a[j]`, whose side condition is decided
  against the facts, does (see
  [single_elem_safe.dfy](benchmarks/sv-comp/dafny/array-lopstr16/single_elem_safe.dfy)).
- Conditionals inside equations and products are not lifted, e.g.
  `(if c then x else n) == (if c then x * x else n)`; a lemma for equations of
  conditionals with the same test applies, but one for the product
  `(if c then x else y) * (if c then x else y)` does not match, presumably
  since products of conditionals are monomials of the polynomial (see
  [motivex.dfy](benchmarks/sv-comp/dafny/array-lopstr16/motivex.dfy)).
- Facts with coefficients are not combined: `n₁₄ <= 200000` and
  `100000 < n₆` do not give `n₁₄ < 2 * n₆`, since difference constraints
  have unit coefficients; nor is an interval `100000 < n₆ < 100002` on Int
  narrowed to `n₆ == 100001` (see
  [array_doub_access_init_const.dfy](benchmarks/sv-comp/dafny/array-cav19/array_doub_access_init_const.dfy)).
- A pattern sum of a rule variable and a bound variable, e.g. the position
  `c - k` of a store in an update, matches only if the variable takes a single
  summand: `S + -k` matches, `2 * S + -k + -1` and `S + -k + -1` do not, nor
  does the pattern `c - 1 - k` (see
  [array_tiling_tcpy.dfy](benchmarks/sv-comp/dafny/array-cav19/array_tiling_tcpy.dfy)).
- A lemma for a monomial with a coefficient, e.g.
  `2 * ((-x + x * x) / 2) == -x + x * x`, does not match that monomial inside
  an equation, `n * n == 2 * ((-n + n * n) / 2) + n`, presumably since
  equations are normalized as differences of polynomials (see
  [ps2-ll.dfy](benchmarks/sv-comp/dafny/nla-digbench/ps2-ll.dfy)).
- Conjunctions are matched in order, not modulo commutativity: a pattern `R && A && B ==> C`, with a variable `R`
  for the other premises, matches `u < 3 && A && B ==> C`, but neither `A && u < 3 && B ==> C`, nor
  `A && B && u < 3 ==> C`, nor `u < 3 && B && A ==> C`; further variables between them, `R1 && A && R2 && B && R3`,
  do not help. Lemmas that need two premises of a goal therefore depend on the order in which the simplifier
  emits them (see [seq-3.dfy](benchmarks/sv-comp/dafny/loop-invgen/seq-3.dfy), where the order fits). Chains of comparisons are
  conjunctions already (the parser resolves them), only printed as chains. Premises are looked up at any position
  as side conditions instead (`Rewrite.conditions`), also comparisons, e.g. `requires 2 * a + p <= b + 2 * c &&
  c < a` with `ensures (p + 1 < b) <==> true`, as in MADWiFi-encode_ie_ok; this form does not work for seq-3,
  whose rule `0 < a + b` also matches a single summand and decides its side condition by itself.
- No integer rounding: `2 * n <= 2 * k + 1` does not give `n <= k`; no
  cancellation of a factor, e.g. `k * j < 1000000 * k`, and a lemma
  `if 0 <= k then (k * a < k * b) <==> (0 < k && a < b)` does not match it,
  since a variable of a pattern does not match the coefficient 1000000 of the
  monomial `1000000 * k` (see [count_by_k.dfy](benchmarks/sv-comp/dafny/loop-new/count_by_k.dfy)).

## Performance

Measured on binary search and on the SV-COMP examples
(`benchmarks/sv-comp/dafny`):

- The rewrite steps per command are limited to 1000 (`Context.withRules`),
  and an exhausted budget is reported as "rewriting does not terminate",
  like a stack overflow, although rewriting may terminate.
- The negation of an equation on Int asks the context for both bounds (`Simplify.not`), which made 14 SV-COMP tasks
  time out, one of them closed before (`string-1`); a cheaper check would only look at the bounds that the
  difference constraints already have.
- Guards of updates are decided by the simplifier with all rules
  (`Rewrite.guard`, `Rewrite.holds`), about 20 ms each. Failing decisions
  are the expensive ones, and identical decisions are repeated without a
  cache: 864 decisions, 15 of them distinct, in one run of binary search.
- `Rewrite.conditions` simplifies each conjunct of a side condition, also
  one in which no variable is instantiated yet. Then it rewrites the open
  pattern with all rules, e.g. `X == trace(...)`.
- Matching an equation tries both orders. With the definition of a variable
  (`Context.↑`), `X == trace(...)` matches `Lo == trace(...)` twice, the
  second time with `X` bound to the trace.
- Each round of the fixpoint of `Simplify.apply` simplifies the whole
  formula again. Programs with many loops grow accordingly, e.g.
  [standard_copy9_ground-2.dfy](benchmarks/sv-comp/dafny/array-examples/standard_copy9_ground-2.dfy)
  takes about 20 s for a chain of nine copies, against about 2 s for one copy.
- Non-termination is detected by a stack overflow only, after 8 to 13 s,
  e.g. on counts over prefixes (see Bugs). The symbolic execution of `-teq`
  is exponential in sequences of conditionals and overflows at ten (see Bugs).

## Trace equation systems (`-teq`)

- The runs of the Dafny translations of SV-COMP (`Dafny.unreach-call.Unbounded`, 2 min, 2026-10-10 16:13 against
  15:25): `array-lopstr16/flag_loopdep_simple` is no longer proved (also not with `-fallback`), not because of
  the merged `mod_two_not_zero`; whether the other lemmas of 9a13ed0f or the eta reduction of 97c533c7 is open;
  `loops/vogal-2` reports rewriting does not terminate (one goal locally) since its table of vowels is filled by a
  loop. `loop-crafted/simple_array_index_value_1-1` was open by `mod_two_not_zero`, which is local again.
- The C programs of the translations (`benchmarks/sv-comp/c`) differ from their Dafny sources in 42 of the 270 rows
  of the databases: 32 have lemmas of their own in the Dafny file, which the C file does not contain (mostly closed
  in Dafny, one goal in C); the other 10 differ by the shape of the program that the C frontend builds, e.g. a block
  around the locals of main (`loop-new/gauss_sum`, `half`, `loops-crafted-1/sumt4`, `array-tiling/revcpyswp2`,
  `skipped`, `skippedu`, `array-crafted/zero_sum_const_m2`, `array-programs/partial_mod_count_limited_1`,
  `array-examples/sanfoundry_02_ground`, `sanfoundry_10_ground`).
- Loops bounded by small constants remain in 10 translations (`loop-lit/bh2017-ex1-poly`, `cggmp2005b`,
  `hh2012-ex3`, `loop-invgen/id_build`, `loop-simple/nested_1b`, `loops/eureka_01-2`, `invert_string-3`,
  `sum04-1`, `sum04-2`, `vogal-2`), some asserting the bound, e.g. `k == 4` after `while k <= 3`.
- The functions on traces are declared only by the lemma database
  ([teq.dfy](resources/cuvee/teq.dfy)), whose names may clash with the input,
  and which only Dafny inputs can use (`Config.features`).
- The guards of the updates of traces are the branch conditions of the body
  only; the loop test and assumptions in the body are recorded in `invs`
  (`TEQ.loop`), which the simplifier and the matching assume in the update of
  `X == trace(...)` (`Simplify.invariants` with `self`), but not for traces
  that are not the right-hand side of such an equation.
- The guarded cases of an expression are matched in their order, each against
  some case of the pattern, such that a higher-order guard bound by a later
  case of the pattern is still open when an earlier case of the expression
  needs it.
- Facts about terms are not derived (see [doc/simplifier.md](doc/simplifier.md#forward-reasoning));
  bsearch.dfy needs a cut, `assert φ; assume φ;`, and `-teq`
  does not assume assertions.
- The simplifier evaluates integer division on literals and divides by
  literals on Real, but knows no bounds of division, e.g. `l <= (h + l) / 2`
  for `l <= h` is a lemma in bsearch.dfy, nor cancels factors,
  e.g. `2 * n / 2` (see
  [mlceu2.dfy](benchmarks/sv-comp/dafny/array-tiling/mlceu2.dfy),
  [array_of_struct_ptr_monotonic.dfy](benchmarks/sv-comp/dafny/array-industry-pattern/array_of_struct_ptr_monotonic.dfy)).
- Solutions of arithmetic equations are inlined into polynomials only
  (`Chains.solved`), not substituted elsewhere, e.g. `forall x. x == y + 1
  ==> p(x)` stays; a solution that depends on its variable through the
  equations of the context is not inlined (`Chains.acyclic`).
- The selection of the dependencies of a pattern is not backtracked when a side condition fails: a lemma whose
  left-hand side binds `ks` to the first matching dependency (`⌊K⌋`) and whose side condition needs the fragment
  whose first dependency is another list (`⌊R⌋`, selected since the initial value `X(k)` matched its bound variable)
  fails, hence the variant `invs_current_counter_other` with an independent first dependency
  (see [nested_mult.dfy](examples/dafny/algorithms/nested_mult.dfy)).
- A bare bound variable on one side of the body of an `invs` pattern is synthesized as a map (`Rewrite.instantiate`):
  `invs(for ks, js check k, j :: n <= j)` matches every comparison fragment and
  `invs(for ks, Ns, js check k, nn, j :: j == integer(nn))` every equation fragment with `integer` of a bound
  variable (`r' == r + integer(nn)`), with `js` a map over the fact's dependencies; as a left-hand side with `invs`
  side conditions both cycle (the exit lemma of the `nested` module, found by pair runs of its lemmas on
  cocktail_sort.dfy, NOTES.md finding 29); a function symbol on the side of the bound variable,
  `invs(for ks, Ns check k, nn :: integer(nn) <= n)`, is specific. `Rule.check` could reject a left-hand side whose
  body has a bare bound variable of a variable dependency together with an `invs` side condition.
- A bound that is not a difference constraint is not decided from two facts: `len <= 2 * integer(m) + 1` from
  `n <= integer(m) + lo + 1` and `lo == integer(m)` (cocktail_sort.dfy states the bound in the goal's form with `lo`
  an open variable).
- A polymorphic lemma with a higher-order variable in a side condition is not matched: `current_results_steps<a>`
  with `F: (a, int) -> a` (or `F: a -> a`) never fires, the monomorphic lemma does; `X: a -> int` in a side
  condition is matched, so the problem is a higher-order variable of the type parameter's type
  (see [nested_mult.dfy](examples/dafny/algorithms/nested_mult.dfy), [transpose.dfy](examples/dafny/algorithms/transpose.dfy)).
- A literal disjunctive guard `n <= j || i < m && a[i] <= b[j]` in a trace pattern is never matched, while a
  higher-order guard `G(i, j)` is, pinned by a quantified side condition `forall i, j :: G(i, j) <==> ...` that the
  simplifier decides by beta reduction; the same pin serves for every literal pattern that is not matched (`j - 1`
  as a store index, `n - k - 2` as an initial value), see [merge.dfy](examples/dafny/algorithms/merge.dfy),
  [insertion_sort.dfy](examples/dafny/algorithms/insertion_sort.dfy), [cocktail_sort.dfy](examples/dafny/algorithms/cocktail_sort.dfy).
- A higher-order variable for an array read, `G(i)` against `a[i]`, is instantiated by the array itself, and the
  right-hand side then contains `a(i)`, which no lemma matches
  (see [prefix_sums.dfy](examples/dafny/algorithms/prefix_sums.dfy), which reads the array literally instead).
- A variable argument of an uninterpreted function is not expanded by its definition when a pattern is matched
  below it: `sorted(c, 0, n)` with `c == current(C)` is not matched by a left-hand side `current(trace(...))`, but
  the whole atom `sorted(current(trace(...)), 0, s)` is, likewise `selects(current(...), ...)` with `selects` as
  the head inside `count`; the length must then be a variable `s` with `s == m + n` as a side condition, since a
  pattern `m + n` of two variables is not matched (see [merge.dfy](examples/dafny/algorithms/merge.dfy)).
- A closed side condition that equates a list with a trace, `is == ⌊trace(0, for ⌊counter(0, 1, nn)⌋, js do ...)⌋`,
  is decided by the simplifier and fails, since `⌊I⌋` is not expanded; the same with an open trace variable,
  `Iv == trace(...)` matched against the hypothesis `I == trace(...)` and then `is == ⌊Iv⌋`, works, also for
  `Iv == counter(0, 1, n)` (see [merge.dfy](examples/dafny/algorithms/merge.dfy), [counting_sort.dfy](examples/dafny/algorithms/counting_sort.dfy)).
- A quantified hypothesis `forall i :: 0 <= i < n ==> 0 <= a[i] < k` is matched by no side condition, open or
  closed; the specification states it as an atom `keys_below(a, n, k)` instead
  (see [counting_sort.dfy](examples/dafny/algorithms/counting_sort.dfy)).
- Arithmetic premises of a quantified side condition are substituted before the step lemmas see it: `i == k + 1` in
  `forall b, k, i :: ... && i == k + 1 && ... ==> sorted(F(b, k, i), 0, i + 1)` turns the conclusion into
  `sorted(insert(b, k + 1), 0, k + 2)`, which the pattern `sorted(insert(b, i), 0, i + 1)` does not match
  (see [insertion_sort2.dfy](examples/dafny/algorithms/insertion_sort2.dfy), whose induction drops the premise).
- Higher-order patterns (`Rewrite`) take distinct bound variables or terms
  instantiated already as arguments; other arguments match only if an
  earlier occurrence instantiated the variable, and a single bound variable
  of the pattern cannot abstract several of the expression (no tuples).
  Terms are abstracted at all of their occurrences.
- Lemmas whose left-hand side is an `invs` with a bare comparison or equation as the body and a dependency that
  is a variable, e.g. `above_iterations_def` (`k < t`), match every fragment with such a body, with the dependency
  synthesized as a map: a resolved constraint `k + 1 + integer(nn) <= n` of an inner loop is consumed as
  `above_iterations(n, maps(... n - integer(nn)))`, and an atom for the exit of a pass,
  `invs(for ks, js check k, j :: n <= j + k + 1) <==> exits(ks, js, n)`, matches `2 k + 1 < n` and `0 <= integer(nn)`
  (see [cocktail_sort.dfy](examples/dafny/algorithms/cocktail_sort.dfy), [selection_sort.dfy](examples/dafny/algorithms/selection_sort.dfy),
  which keeps the raw constraint as a side condition). Such definition lemmas should have a body that the matcher
  cannot synthesize, e.g. an `earlier` read as in `consts_prefix_def`.
- The fragments of an inner loop are resolved by generic lemmas (the inner trace over the inner counter is a counter,
  its final value, the test, the exit, the lengths as a constant sequence), see
  [fragments.dfy](examples/dafny/algorithms/fragments.dfy), candidates for teq.dfy; they are what the sharing of facts
  of 7b420a0 did, as rewrite rules. Likewise `results` with `current_results_steps` for the outer trace of a variable
  that only the inner loop modifies, `current_trace_all`, `current_trace_histogram`, `current_trace_prefix_sums_array`,
  and the lemmas on `perm` (see [NOTES.md](examples/dafny/algorithms/NOTES.md), the entry of Oct 11 for their
  termination analysis).
- Induction lemmas with the invariant as a predicate indexed by the iteration, `bubbled(b, k, len)`, and a
  quantified side condition `forall b, k :: 0 <= k < integer(m) && I(b, k) ==> I(F(b, k), k + 1)` that the simplifier
  decides by step lemmas on atoms, replace whole-loop lemmas of sorting algorithms; the number of steps must be
  constrained exactly or the invariant clamped, since steps beyond the range are unconstrained otherwise
  (see [bubble_sort.dfy](examples/dafny/algorithms/bubble_sort.dfy), [selection_sort.dfy](examples/dafny/algorithms/selection_sort.dfy)).
- No instantiation of the iteration constraint at a witness, e.g. a search
  whose constraint states that `P` holds before the exit `n`, and `!P(j)`,
  which gives `n <= j`; the examples abstract the constraint by an atom first,
  e.g. `!occurs(e, selects(a, ⌊counter(0, 1, n)⌋))` by `not_occurs_selects_def` of teq.dfy, which a second lemma
  takes as its side condition (see
  [standard_sentinel-2.dfy](benchmarks/sv-comp/dafny/array-examples/standard_sentinel-2.dfy)),
  since a side condition that is an iteration constraint does not terminate.
- Nested loops: the outer trace takes the values of summarized inner traces,
  whose composition, e.g. `k == n * m`, is not accelerated (see
  [nested-1.dfy](benchmarks/sv-comp/dafny/loop-new/nested-1.dfy)).

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

- Integers are unbounded, signed overflow is not modelled; arrays are
  values, sizes are ignored. Expressions have the integer types of C
  (`c.IntType`: signedness and rank, sizes by `-arch`), with the integer
  promotions and the usual arithmetic conversions (`c.Parser.common`).
- Unsigned integers wrap around: the results of `+`, `-`, `*`, and `<<` in
  an unsigned type, and conversions of values to one (assignments,
  arguments, returns, casts, operands of a common unsigned type, e.g.
  `-1 < 1u` is false) apply the overflow function of its size, `uchar`,
  `ushort`, `uint`, `ulonglong` of the prelude (`x mod 2^n`, rw), unless the
  value fits (`c.Parser.convert`); the printer prints them as casts.
  Unsigned loop counters, `x = uint(x + 1)`, are no counters for `-teq`,
  which does not accelerate them (see `examples/c/teq/from.c`, run with
  `-unbounded`).
- The values of `__VERIFIER_nondet_<type>()` are within the range of their
  type, for `char`, `short`, `int`, `long`, `longlong`, their unsigned
  versions, and `size_t` (`c.Parser.havoc`). Variables declared without a
  value are arbitrary integers.
- `-unbounded`: neither ranges nor overflow, only the values of unsigned
  nondeterministic functions are nonnegative, as before.
- `goto` only to a label whose statement does not fall through (e.g.
  `END: return 0;`, `ERROR: { reach_error(); abort(); }`), which is copied in
  its place, or to itself (a loop without exit); other gotos, e.g. those of
  state machines, are not supported (`c.Parser.goto`).
- `sizeof` of an expression by the declared integer type and array sizes of
  its variable (`c.Parser.bytes`), otherwise by its type.
- No structs, floating point, bitwise operators, preprocessor; pointers
  only as arrays allocated by `malloc`, `alloca`, `calloc` (see [SV-COMP.md](SV-COMP.md)), and otherwise as values of `Ptr`
  in the prelude of C ([prelude.bpl](resources/cuvee/c/prelude.bpl)), which
  are compared but not dereferenced; no `&`, `*p`, or pointer arithmetic.
- The modifies clause of a loop is inferred from the core program, where a
  local variable that shadows a global one of the same type counts as global.
- ACSL annotations (0.38.0, `/*@ ... */` and `//@`): function contracts
  `requires`, `ensures` (`\result`, `\old`), `decreases`; `loop invariant`,
  `loop variant` before `while`, `for`, `do`; `assert`; terms with `==>`,
  `<==>`, `\forall`/`\exists` (variables of C types range over the type,
  except with `-unbounded`, `integer` and `boolean` unbounded), chained
  comparisons, mathematical arithmetic without wrap-around, casts as in C.
  `assigns` and `loop assigns` are the modifies clauses of their functions
  and loops (their identifiers, the global ones; locals are inferred), which
  the body must respect, except with `-teq` and `-chc`, which infer the
  modifies clauses (0.41.5; before, the clauses were skipped). `\at(e, L)` for `Pre`, `Here`, `LoopEntry`, `\valid` and
  `\valid_read` (true), ranges of unsigned parameters of functions with
  annotations as preconditions as in Frama-C/WP (those of the unsigned
  variables that loops modify are no implicit invariants since 0.41.6), and
  `&`, `|`, `^` of truth values (0.39.3). Global declarations (0.40.0):
  `axiomatic Name { ... }`, whose name is dropped (it groups, it does not
  scope), and the same declarations outside of one: `logic T f(params)` and
  `predicate p(params)`, uninterpreted or `= body` (also recursive), with
  `reads` skipped, as `DeclareFun`/`DefineFun`; `axiom name: phi;` as
  `Assert(Axiom)`, `lemma name: phi;` as `Assert(Lemma)` with `:free`
  (trusted, inductive lemmas are beyond z3), both `:named`; calls of logic
  functions in terms; pointers in logic signatures and quantifiers are
  arrays (`int *a`, `int **m`); logic declarations cannot refer to program
  variables (pass them as parameters). Not supported: other `\...`
  constructs (`\separated`, other labels, ...), labels of lemmas
  (`lemma l{L1, L2}`, state them over two arrays), behaviors, ghost code,
  calls of C functions in annotations; contracts of `main` are conjoined
  with the zero values of the globals. The printer writes contracts, loop
  invariants and variants, and assertions that are not C (quantifiers,
  implications, `\old`, calls of logic functions) as ACSL, and functions
  (`DeclareFun`, `DefineFun`), axioms and named lemmas as global ACSL
  declarations. Step axioms of recursive definitions are best stated
  backwards, `n > 0 ==> f(a, n) == f(a, n-1) + a[n-1]`: z3 cannot trigger on
  `f(a, n+1)` (`+` is interpreted) and unfolds `f(a, n)` forever.
- ACSL on SV-COMP ([benchmarks/acsl](benchmarks/acsl), the tasks of the
  categories Arrays and Loops with hand-written annotations, checked with
  `-vcgen -z3`, 0.38.0; the issues of the support found so far, by impact):
  - Done in 0.39.3 for unsigned types: annotated loops get the ranges of the
    unsigned variables they modify as invariants, functions with annotations
    those of their unsigned parameters as preconditions (`c.Parser.loop`;
    `count_up_down-1`, `trex03-2` prove); signed types get none, as their
    overflow is not modelled. Undone for loops in 0.41.6: the ranges of the
    modified variables are no implicit invariants, the annotations state them
    as loop invariants where needed (the implicit ones also constrained
    uninitialized locals, see below). Was: the ranges of the C types of the program
    variables are not assumed at loop heads: the state is quantified over all integers, while the program
    wraps unsigned arithmetic (`uint(x + 1)`), so a loop invariant over
    unsigned variables, e.g. `x + y == n` (`loops/count_up_down-1`), is
    refuted by a negative `x`. Frama-C/WP conjoins the type ranges to every
    invariant implicitly; `loop-invariants/linear-inequality-inv-a` proves
    with an additional `0 <= s`. Affects nearly all of `loops-crafted-1`
    (43 of 55 refuted), `loop-crafted/simple_vardep_*`, `loops/trex03-2`.
  - Done in 0.39.3 for truth values: `&`, `|`, `^` of two truth values are
    `and`, `or`, xor (`c.Parser.logical`; the `*_abstracted` tasks prove); `&`
    with other operands remains `bitand` (`bin-suffix-5`). Was: bitwise `&` is
    uninterpreted (`bitand`), also on operands that are 0 or 1: the `*_abstracted` tasks test `(z > 100) & (x < 100)`
    (`loops/terminator_02-2_abstracted`, `trex03-2_abstracted`), and
    `loop-invariants/bin-suffix-5` asserts `(x & 5) == 5` with the invariant
    `x % 8 == 5`.
  - Done in 0.39.3: `\at(e, Pre)` is `\old(e)`, `\at(e, Here)` is `e`,
    `\at(e, LoopEntry)` reads copies assigned before the loop; `\valid` and
    `\valid_read` are true. The `axiomatic` remains. Was: not supported but
    used by the annotations: `\at(x, LoopEntry)` and
    `\at(x, Pre)` (`loop-crafted/simple_array_index_value_4`, `loops/nec20`,
    `trex02-2`), `\valid`/`\valid_read` in preconditions of functions on
    arrays (`loops/linear_sea.ch`, `linear_search`, `veris.c_NetBSD-libc_loop`;
    could be accepted and ignored, memory safety is not checked), an
    `axiomatic` with a recursive logic function (`loops/vogal-1`, the number
    of vowels of a prefix; ends in a generic parse error).
  - A refuted goal is printed as one SMT-LIB string, `(error "goal does not
    hold" "Sat" "(forall ...)")`, without the annotation (loop invariant,
    assertion, postcondition, line) that failed; `-vcgen -z3` prints
    nothing when all goals hold.
  - Done by the annotation (Oct 12, 2026): `loop-new/count_by_k` proves with
    `k == 0 ==> i == 0` and `k > 0 ==> i % k == 0`. Was: the invariant
    `\exists integer q; 0 <= q && i == q*k` is `Unknown`.
  - Done in 0.40.1: an assertion is assumed once it is checked, `phi && (phi
    ==> post)` ([VCGen](src/cuvee/verify/VCGen.scala), case `Spec`;
    [assert_assumed.c](examples/c/vcgen/assert_assumed.c)), as in Frama-C/WP
    and Boogie, for all frontends; the reducers (`array-crafted/bAnd5` etc.)
    with `//@ assert ret2 == ret;` now prove with `-split` as well. Was: `phi
    && (true ==> post)`, equivalent, but z3 does not have `phi` in the branch
    `!post`, and `-split` makes `post` a goal of its own without `phi`; the
    reducers proved only because z3 kept the quantifier instances of the
    assertion's proof in the same query.
  - `-verify` answers `incorrect` to goals refuted through uninterpreted C
    operators (`shl`, `shr`, `bitand`, `bitor`, `bitxor`, `bitnot`), whose
    models need not be counterexamples (`shl(1, 0) != 1`): of the 87 true
    tasks of benchmarks/acsl with a refuted goal in the 0.40.0 run, 51 refute
    an annotation with such an operator (the powers of 2 `\exists integer k;
    ... p == 1 << k` of `nla-digbench*`), wrong `false` answers under
    `-verify` (`nla-digbench-scaling/hard-ll_valuebound100`,
    `divbin2_unwindbound10`, Oct 12, 2026); none remain in benchmarks/acsl
    since the powers of 2 and 4 are predicates with goal-directed axioms
    (`pow2`, `pow2mul`, `pow4`, 50 tasks, 37 of them proved). Done in 0.42.1:
    the operators are declared `:abstract` in the C prelude, `pipe.Verify`
    takes the refutation of a goal that applies them (`Cmd.funs`) for
    `unknown` ([teq_bits_abstract.c](examples/c/verify/teq_bits_abstract.c)).
    Open: interpret the operators where possible (shifts of constants as
    multiplications by powers of 2, masks of low bits as `%`).
  - Done in 0.41.6 by dropping the implicit ranges of loops (see above). Was:
    uninitialized locals of unsigned types are not in the range of their type:
    a loop whose `loop assigns` contains one checks its range at the entry
    (the ranges of the modified unsigned variables are invariants, see above),
    which fails for `unsigned int i, j;` before `j` is assigned
    (`loops/vogal-1`, `heavy-2`, `matrix-1`,
    `veris.c_sendmail_tTflag_arr_one_loop`, all prove with the locals
    initialized). A declaration without initializer could choose a value in
    range, as C's indeterminate values are. Under `-verify` the refuted range is
    `incorrect`, a wrong `false` (`heavy-2`).
  - Contracts of functions that read globals need the globals' values as
    preconditions (`loops/eureka_05`, `requires n == 5`), as in Frama-C; a
    contract on `main` is the only one that sees the initial values.
  - `\min`, `\max`, `\abs` are not supported (the scanner rejects them);
    `array-programs/partial_mod_count_limited_*` write `\min(a, b)` as the
    conditional `(a <= b ? a : b)` instead (Oct 12, 2026). Done in 0.40.0: logic
    functions in an `axiomatic` and lemmas (the labels of lemmas and the
    flattened matrices restated in the annotations, see below); the memory
    clauses (`\valid`, structs) are removed from the annotations.
  - Z3 answers `Unknown` on nonlinear closed forms: `nla-digbench/geo*`
    modulo 2^64, `lcm2`, `prod4br`; `array-programs/partial_mod_count_2-5`
    (counts with integer division); `array-patterns/array26` (parity of a
    count). `array25`, `array27`, `array29`, `array30` with cubic closed
    forms are proved.
  - Function parameters of unsigned types are not in range either
    (`loop-acceleration/functions_1-1`, `ensures \result == z + 2` with
    `uint(z + 2)` in the body is refuted for negative `z`). Done in 0.39.3 for
    functions with annotations: `functions_1-1` proves.
  - Runs under CPU load time out at 10 s on trivial tasks (`loop-lit/mine2017-ex4.6`
    proves in 2.6 s alone); the limits of the runs in the README are not
    those of the tool.
  - Open in the frontend (0.39.4): `&` of operands that are not truth
    values stays `bitand` (`bin-suffix-5`, `(x & 5) == 5` with `x % 8 == 5`;
    could be `x % 8` for constant masks of low bits); labels of `\at` other
    than `Pre`, `Here`, `LoopEntry`; `-chc` answers `unknown` on the unsigned
    arithmetic modulo 2^n of annotated programs
    ([acsl_ranges.c](examples/c/vcgen/acsl_ranges.c) is checked with
    `-vcgen` only).
  - Deferred: array parameters that a function assigns as in/out parameters. Arrays are values in Cuvée's C
    and ACSL, so `void incrementArray(int src[N], int dst[N])` assigns a copy of `dst`: its `ensures dst[t] ==
    src[t] + 1` speaks of the value passed in (z3 answers `Unknown`, quantified), and the caller's `dst` stays
    unchanged after the call, while C passes a pointer (`array-examples/sanfoundry_43_ground`, 0.39.5, without
    its `\valid`, `\valid_read`, `\separated`). In/out parameters, whose final value the caller receives and
    `ensures` refers to, are sound when the arguments do not alias, which `\separated` states in Frama-C and
    distinct variables as arguments would ensure here. The memory clauses of the annotations are removed
    (`\valid`, `\valid_read`, `\separated`, `\null`, 64 files of benchmarks/acsl): pointer reasoning is not
    needed in this dialect; the two tasks with
    `\null` (`array-industry-pattern/array_ptr_partial_init`, `array-lopstr16/partial_lesser_bound`) end in
    "arrays of pointers are not supported".
  - Results: 603 of the 838 true tasks proved with 0.40.0 (60 s, Oct 12, 2026; 534 with 0.39.5), none wrong;
    693 with the annotations of 90 tasks revised since (single runs; 37 of `hard-ll`, `hard2`, `divbin`, `divbin2`
    with predicates for the powers of 2 instead of shifts, 41 refuted or weak annotations corrected, `\min` as a
    conditional in `partial_mod_count_limited_*`, `partial_mod_count_limited_gen` with `-split`); the 323 tasks expected
    `false` are removed (Oct 12, 2026), 838 remain;
    per folder and the causes of the others in [benchmarks/acsl/README.md](benchmarks/acsl/README.md).
  - Done in 0.40.0: the parse errors of `xml/cuvee-acsl.xml` (60 s, 0.39.4, Oct 12, 2026; 131 tasks). The 95
    global logic declarations (`axiomatic Fold` 53, `Asum` 18, `Msum` 14, `Sum` 9, `Count` 1) are supported
    (see ACSL annotations above), with the annotations restated: no `reads`, step axioms backwards, the lemmas
    with labels over two arrays, `Msum` over `int **a` instead of the flattened matrix, the labels `L1`, `L2`
    of the reducers and their assertions removed, `\at(e, LoopEntry)` in the rotation loops, the global `N` a
    parameter of `fold` in `rangesum`. The 37 tasks with structs (33 parse errors, 3 with a field selector after
    a range in `assigns`, `relax-2-2`) are removed from benchmarks/acsl (see its README).
- z3 answers `unknown` for Horn clauses with division by variables
  ([examples/c/vcgen/div.c](examples/c/vcgen/div.c)), and for calls in loops whose
  callee has no goals, since its precondition is inferred from the calls
  (only the entry point has a precondition of its own, see `-entry`).
- Errors of the C frontend on SV-COMP (Arrays and Loops, 0.34.22, 101 tasks;
  with 0.35.2, 3 parse: `loops/compact`, `heavy-1`, `heavy-2` by `sizeof` of
  expressions), besides `goto` to labels that fall through (26, see New;
  most are gotos back in the outputs of the reducers, which could be loops
  `L: while (true) { ...; break; }` whose gotos continue them, without
  copies), and floating point (29, also float literals now report "not
  supported"):
  - Structs and unions end in a generic parse error, not in "not supported"
    (37 tasks: definitions and forward declarations `struct S;` at the top
    level, `typedef struct {...} *T`, an anonymous `struct { int n; } a[]`
    as parameter, e.g. `array-lopstr16`,
    `array-industry-pattern/array_of_struct_*`, `loop-industry-pattern/aiob_*`,
    `ofuf_*`, also `union wait` of the headers in `array-examples/relax-2-2`).
  - Deeply nested `if`/`else` (about 240 levels in the outputs of the
    reducers) overflowed the stack; `Cuvee.main` now runs on a thread with a
    stack of 1 GB, and `c.Parser.effects` iterates over the statements of a
    block; these tasks now end at gotos. Tests call `Cuvee.pipe` directly,
    on the default stack.
  - `*p` in `p <= tmp` with pointers is "not an integer"
    (`loops/verisec_NetBSD-libc_loop`, `veris.c_NetBSD-libc_loop`); `&x` and
    `*p` otherwise report "not supported".
  - Arrays of pointers are not supported (`array-industry-pattern/array_ptr_partial_init`,
    `array-lopstr16/partial_lesser_bound`).
  - A pointer that is assigned a local array, `char in[11]; char *s; s = in;`,
    is a type mismatch of `PointerType` and `ArrayType`
    (`loops/veris.c_sendmail_tTflag_arr_one_loop`).
  - GCC builtins are unknown functions, e.g. `__builtin_bswap32`
    (`array-examples/relax-2-2`).

## Portfolio of TEQ and CHC (SV-COMP)

The configurations complement each other: in the runs of Oct 11, 2026 on
ReachSafety-Loops, `-chc -z3` (1 min, `xml/cuvee-chc.xml`) proves 146 tasks
and `-teq` (2 min) 123, together 195; on ReachSafety-Arrays 8 and 133,
together 137. Only `-chc` reports violations (85 correct, none wrong), since
`unsat` of the Horn clauses is a counterexample, whereas a model of Z3 for a
goal of `-fallback` is none (the encoding abstracts the goal, `cuvee.py`
scores it unknown).

- A portfolio in Cuvée, e.g. an option that `cuvee.py` passes with the time
  limit (BenchExec's rlimits): the steps in sequence, not in parallel, since
  BenchExec counts the CPU time of all cores against one limit, e.g. `-teq`
  for a short slice (usually fast or stuck), then `-chc` for most of the
  remaining time, then `-fallback` with the rest; the slices from the CPU
  times of the 15-minute runs; parsing shared between the steps.
- Disagreement is unknown: a proof by `-teq` and `unsat` by `-chc` indicate
  a bug in one of them, and wrong results cost 32 (true) and 16 (false).
- Soundness of `sat` with `-chc`: the prelude declares the bit operations
  (`bitand`, `bitor`, `bitxor`, `bitnot`, `shl`, `shr`) without definitions,
  so Z3 may choose their interpretation in clauses that use them and report
  them satisfiable for a program that is not safe; `sat` should count only
  if the clauses use no such function, which Cuvée can check.
- Witnesses (see "witness output" above): SV-COMP scores verdicts without a
  validated witness with 0. The model of Z3 for the Horn clauses gives the
  loop invariants of a correctness witness, its counterexample the path of a
  violation witness; `-teq` would need invariants from the trace equation
  systems.

## SV-COMP task definitions

- The properties and expected verdicts of a task (`Task.properties`) are read
  but not used; only a single input file in C is supported.
- The C versions of the local benchmarks (`benchmarks/sv-comp/c`) are patched
  by nondet.py, sizes.py, and bounds or conditions on the inputs of 34 tasks
  (see [false-verdicts.md](benchmarks/sv-comp/c/false-verdicts.md)); open:
  - not checked by a full run: of the patched tasks, 10 of group 2 have not
    run again (eureka_01-2, array_init_nondet_vars,
    array_min_and_copy_shift_sum_add, mono-crafted_6,
    linear-inequality-inv-a, -c, -d, hard-ll, underapprox_1-2, mod3) and 23
    of group 3; the wrong true verdicts of Symbiotic (57) and AISE (55),
    nearly all in files with uninitialized locals, should be gone with
    nondet.py; Cuvée has not run on the patched files, and their
    `expected.csv` predates the patches.
  - 9 tasks that only AISE finds false, without a known cause (group 4:
    bAnd5, bor5, xor5, mapsum5, mapavg5, sanfoundry_10_ground, init-2-n-u,
    gj2007, mono-crafted_1); AISE's first stage fails (`bin/runexec`
    missing), so these verdicts come from its KLEE fallback.
  - The Dafny translations lack the patches
    ([c_patches.diff](benchmarks/sv-comp/dafny/c_patches.diff)); printing the
    C versions again undoes them. The expected verdict true of the group 1
    translations is wrong without their conditions.
  - partial_mod_count_limited_gen assumes `N % 60 == 0`, which suffices but
    is stronger than needed.
  - geo1-u is unsafe only by the wrap-around of `unsigned long long`, which
    Cuvée+Z3 and Korn prove safe (see Bugs).
  - 5 translations lose an update of an array parameter and are excluded
    from the task sets until fixed (see the
    [README](benchmarks/sv-comp/c/README.md)).

## Bitvectors

`BitVec(n)` with the SMT-LIB literals and functions (`BitVecs`). Open: no
simplifier rules; widths cannot be parameters.

- Return to the bitvectors of Dafny: the test suites over
  `examples/dafny/vcgen` (`SimplifyPrograms`, `VCGen`, `Split`) reported
  "goal does not hold" for [bitvectors.dfy](examples/dafny/language/bitvectors.dfy)
  sometimes in the full test run, depending on the tests run before it in the
  same JVM; alone, and with `java -jar cuvee.jar -simplify -vcgen -z3`, it
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
