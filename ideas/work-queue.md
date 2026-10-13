# Work queue of the database migration and the engine

The open items of the current work (Oct 13, 2026 on), kept up to date; the plans behind them are in
[teq-modules.md](teq-modules.md) (database) and [prove-next.md](prove-next.md) (engine), bugs in
[bugs.md](../bugs.md). Priority: more correct results, `true` first (TEQ is made for proofs, and they score
double); speed only where a task times out that would succeed.

## In progress

- [ ] 15 min runs on the cloud (i7-6700, 0.46.9): `cuvee`, `cuvee-fallback` on Arrays, Loops and the four MonoCera
      sets, `cuvee-chc` on Arrays and Loops (14 calls, started 22:11). Then: the table of doc/paper/cuvee.tex and
      its sources in doc/paper/README.md (`scripts/paper.py`, checked against the numbers of 0.41.4), `scripts/experiments.py` (only 0.46 runs, scatter plots out of the
      document), ideas/experiments.md.
- [ ] The inconsistency of the bisection (bugs.md, open): a premise on `bisection_lo`/`_hi` never matches, a premise
      on the rule `bisection` makes bsearch_bisect.dfy not terminate (the earlier "0 goals" were runs killed by
      the timeout; always check the exit status). Next idea: a third case of the function `bisection` that keeps
      the state, or the premise as a closed condition over the trace's own histories without `hs`.
- [ ] Commit 0.46.12 (suite running): a negative literal is the negation of its absolute value in `Rewrite.summands`
      (`a[i - 1]` of a pattern matches `a[k + -1]`); case splits on disjunctive premises in `Prove.cases`
      (in-de20, in-de41, in-de42, in-de51 close); `select_current_trace_recurrence` in aggregation (ifeqn1, ifeqn2
      close); `store_select_other` (arrays), `maps_counter_scale` (teq.dfy), `occurs_counter_step` (counters).
      Then a cloud run at 60 s against 0.46.9.

## Next, by expected gain

- [x] An overview paper of the whole project (draft: doc/overview/overview.tex; numbers of the 15 min runs to add), high-level and self-contained: exactly the current approach (one
      trace per strongly connected component, `-prove`, the lemma database with its modules, forward lemmas,
      `-fallback`, `-chc`, `-verify`; `-simplify` omitted), for readers who know verification but not TEQ, with all
      major insights (from the docs, ideas/, bugs.md, the experiments).
- [ ] Recurrences in arrays: ifeqn1, ifeqn2 close with `select_current_trace_recurrence`; open: `ifcomp`, `pcomp`,
      `sqm-if`, `nsqm-if`, `condm` (other shapes).
- [ ] Strided stores (array-tiling `mbpr*`, `pr*`, `pnr*`; 22 true tasks): `store_select_other`
      (`a[i := v][j := a[j]] == a[i := v]` for `i != j`), `maps_counter_scale` (`maps(... :: b * v)`, which
      `maps_counter_affine` does not match without a constant), `occurs_counter_step` back from the legacy file
      (scratch stride.dfy; all fire on mbpr2). Open: the parity `(i - 1) % 2 == 0` against `i % 2 == 0`, which
      needs integer reasoning about remainders (the simplex is rational); a forward lemma
      `x % 2 == 0 || (x - 1) % 2 == 0` does not close it.
- [ ] Counterexamples without a solver: a remaining goal without traces and uninterpreted functions, e.g.
      `forall N :: !(0 < N && N <= 536870911)` of brs1f, refuted by evaluation at candidate values (the `f`
      variants of array-fpi, while_infinite_loop_4; expected false, lower priority).
- [ ] The tasks lost against 0.42.1: in-de52 to in-de62 (try with the case splits), sum_by_3_abstracted (open with
      the case splits), sum_array-2-2, indp5, revcpyswp2 (time outs at 60 s), while_infinite_loop_4.
- [ ] array-patterns (30 true tasks): pairwise cancelling sums over stores at nondeterministic indices; hard.

## Deferred

- [ ] cocktail_sort, counting_sort (do not terminate), the nested sorts with `teq:sorted`, retiring `teq:nested`.
- [ ] The memo of forward instances (cost; bugs.md, prove-next.md).
- [ ] nla-digbench: non-linear arithmetic, beyond the lemma database for now.
- [ ] Lean: proofs of `bisection_lo`/`_hi` under the new premise, the module `unsigned` (the Lean session).

## Last

- [ ] When everything is done: the final integration of the results into the documents (doc/paper/cuvee.tex with
      `scripts/paper.py`, `scripts/out/experiments.pdf`, ideas/experiments.md, doc/overview/overview.tex), commit all
      the work, and only then a single push.
