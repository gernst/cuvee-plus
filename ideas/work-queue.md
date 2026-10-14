# Work queue of the database migration and the engine

The open items of the current work (Oct 13, 2026 on), kept up to date; the plans behind them are in
[teq-modules.md](teq-modules.md) (database) and [prove-next.md](prove-next.md) (engine), bugs in
[bugs.md](../bugs.md). Priority: more correct results, `true` first (TEQ is made for proofs, and they score
double); speed only where a task times out that would succeed. Benchmarks that change are not rerun with Cuvée (the
user's instruction, Oct 14).

## Next, by expected gain

- [ ] SV-LIB (CTranslated, CoreVerification) for section 6 of the experiments, the only section still pending.
- [ ] ps2-ll_unwindbound1 times out with 0.46.13 at 60 s (31 s with 0.46.8).
- [ ] The inconsistency of the bisection (bugs.md, open): a premise on `bisection_lo`/`_hi` never matches, a premise
      on the rule `bisection` makes bsearch_bisect.dfy not terminate (the earlier "0 goals" were runs killed by
      the timeout; always check the exit status). Next idea: a third case of the function `bisection` that keeps
      the state, or the premise as a closed condition over the trace's own histories without `hs`.
- [ ] Recurrences in arrays: open `ifcomp` (three levels, `c[j] == j^3`: a sum of a quadratic over
      `counter(1, 1, j)`, which needs a general sum of squares with an exact division by 6, as a forward lemma like
      `triangle_even`, and products matched modulo commutativity), `pcomp`, `sqm-if`, `nsqm-if`, `condm`.
- [ ] Strided stores (array-tiling `mbpr*`, `pr*`, `pnr*`; 22 true tasks): the rules fire on mbpr2; open is the parity
      `(i - 1) % 2 == 0` against `i % 2 == 0`, which needs integer reasoning about remainders (the simplex is
      rational); a forward lemma `x % 2 == 0 || (x - 1) % 2 == 0` does not close it.
- [ ] Counterexamples with concrete evaluation (expected false, 1 point each): 30 unsafe array-fpi tasks remain,
      e.g. brs2f leaves `sum(map(⌊counter(0, 1, n)⌋, k :: if 0 < k then (if k % 2 == 0 then 20 else 0) else 0)) <=
      2 N`, false at N = 3, which needs `sum`, `map`, `counter` evaluated for a literal n (an evaluator for closed
      instances, not rules).
- [ ] The tasks lost against 0.42.1: in-de52, in-de62 (more loops than depth 4 of the case splits),
      sum_by_3_abstracted, sum_array-2-2, indp5, revcpyswp2 (time outs at 60 s).
- [ ] array-programs partial_mod_count_* (true): conditional stores `case P(k) => a[k := 0] case !P(k) => a[k := k
      + 1]`, whose second value is not a constant, then the count of zeros among the reads.
- [ ] array-patterns (30 true tasks): pairwise cancelling sums over stores at nondeterministic indices; hard.

## Deferred

- [ ] cocktail_sort, counting_sort (do not terminate), the nested sorts with `teq:sorted`, retiring `teq:nested`.
- [ ] The cost of `-prove`: forward instances simplified again at every firing (a memo; the separate budget of
      0.46.8 was reverted), aggregation on polynomial loops (bugs.md).
- [ ] nla-digbench: non-linear arithmetic, beyond the lemma database for now.
- [ ] Lean: the lemmas added since 0.46.12 (`select_current_trace_recurrence`, `store_select_other`,
      `maps_counter_scale`, `occurs_counter_step`, `integer_zero`), the module `unsigned`, the bisection (the Lean
      session).

## Last

- [ ] When everything is done: the final integration of the results into the documents (doc/paper/cuvee.tex with
      `scripts/paper.py`, `scripts/out/experiments.pdf`, ideas/experiments.md, doc/overview/overview.tex), commit all
      the work, and only then a single push.
