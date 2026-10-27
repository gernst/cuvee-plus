# Open classes of SV-COMP ReachSafety-Arrays

The tasks of Arrays that the run `cuvee.incr-0523` (0.52.3, 120 s, one core, Ryzen 7 PRO 5750G, Oct 26, 2026) did
not solve, by the goals that remain, the lemmas that close them, and the gaps of the engine that they work around.
Baseline: 137 true and 62 false correct, 113 true tasks unsolved (41 unknown in array-examples, -programs, -tiling,
-cav19, -industry-pattern alone).

## Lemmas added to the database

All proved in Lean (`scripts/lean/check.sh`), checked locally with the database in the jar (`-cp <resources>:cuvee.jar`)
and without other changes.

| Lemma | Module | Tasks |
|---|---|---|
| `earlier_prefix`: `earlier(j, prefix(k, xs)) == earlier(j, xs)` for `j < k` | teq.dfy | standard_copy1-9, strcpy_ground-1, strcpy_original-2, compareModified, two_index_01 |
| `current_maxs_prefix_earlier`, `current_mins_prefix_earlier` | aggregation.dfy | maxInArray, minInArray-2 |
| `current_trace_row`: an inner loop over one row of a two-dimensional array is an update of that row | arrays.dfy | init-2-n-u, init-non-constant-2-n-u, copy-2-u, copy-partial-2-n-u, rev-2-n-u |

`maps_earlier` makes the values that a loop reads a prefix `prefix(n, xs)`, while the reads after the loop are of the
list `xs`; the first two rows connect them. The outer loop over the rows is `trace_read_initial` of arrays.dfy, which
reads each row from the initial array.

Removed: `store_occurs_selects` (search.dfy), a forward lemma at the reads of every store whose instance, a disjunction
with an occurrence in the values of a store, no rule normalizes, so it came back at every firing (bugs.md; doc/teq.md,
"What a forward lemma costs"). Replaced by `invs_select_store_ne` (search.dfy, proved in Lean), a rule on the
iteration constraint of a search before `not_occurs_selects` folds it:
`invs(for ⌊counter(i, 1, n)⌋ check k :: a[j := x][k] != x) <==> !(i <= j < i + n) && invs(... a[k] != x)`, which
proves standard_sentinel-2 and loop-acceleration/array_4 (8 s each; examples/c/teq/sentinel.c, sentinel_wrong.c). The
same equivalence on `occurs(x, selects(a[j := x], ...))` was the alternative; a rule for stores of other values would
split the counter at the store, which is no form of the programs, and no task needs it.

## Workarounds moved into the database

First injected by an include, now in the modules (proved in Lean); each works around a gap of the engine, named in its
comment and in TODO.md, or is needed by one task only:

| Lemmas | Module | Tasks | Gap of the engine |
|---|---|---|---|
| fold `compacts`, `select_current_compacts_lower/upper` (C[j++] = i) | aggregation | partial_init | terms with binders compared literally by the arithmetic, not modulo the names of bound variables; `⌊K⌋` and `⌊counter(0, 1, n)⌋` not identified below a binder; hence the count is a variable of the conditions and the keys a list |
| folds `filters_above/below`, `select_current_filters_above/below` (bb[b++] = aa[a]) | aggregation | partition_ground-2, partition_original | the same |
| `current_maxs_seeded_earlier`, `current_mins_seeded_earlier` (a maximum seeded with a[0]) | aggregation | sanfoundry_27 | none, one task |
| `select_current_trace_copy_both_ends(_list)` | arrays | tcpy (array-tiling and array-cav19) | rule patterns are not normalized as goals (`m - k - 1` matches nothing, `-k + m + -1` does); a higher-order value `F(m - k - 1)` with an argument other than a bound variable does not match |
| `stores_cases_point` | arrays | copysome2-1 | cases with results equal after substituting the equation of the guard are not merged (`k != c => a[k := F(k)]`, `k == c => a[c := F(c)]`) |

Not moved: the forward lemmas `div_mod` (`x == c * (x / c) + x % c` for `0 < c`) and `mod2_succ` (`(x + 1) % 2 ==
1 - x % 2`), which pr2, mbpr2 and array-tiling/tcpy need: they trigger at every division and every remainder of a
successor, general terms (doc/teq.md, "What a forward lemma costs"), and are the likely cause of the 10 timeouts of
Loops with the fallback; division with remainder and parity belong in the arithmetic of `-prove` (TODO.md).

Tests: examples/c/teq/compacts.c, filters.c, max_seeded.c, copy_both_ends.c, stores_cases_point.c and their `_wrong`
variants.

## Suggestions for the engine

1. Compare terms with binders modulo the names of their bound variables in the arithmetic and in the classes
   (also TODO.md, sumt2).
2. Congruence through binders: `map(k in ⌊K⌋ ...)` and `map(k in ⌊counter(0, 1, n)⌋ ...)` for `K == counter(0, 1, n)`.
3. Normalize the arithmetic of rule patterns as that of goals (`Rule.from`).
4. Higher-order variables applied to terms that are not bound variables, once another case or store binds them.
5. Division with remainder (`x == c * (x / c) + x % c`) and parity in the arithmetic of `-prove`, instead of forward
   lemmas that fire at every division.
6. The normal form of choices: guards in DNF, the merging of cases by results in the matcher
   ([dnf-guards.md](dnf-guards.md)); also merging results that are equal after substituting the guard's equation.
7. Conditional results of traces as cases: done in 0.52.7 (`Simplify.cases`, doc/teq.md, examples/c/teq/ite_cases.c),
   `ite` lifted out of the results with `Normalize.ite`, such that `ret < x[i] ? x[i] : ret` is matched by `maxs`; not
   measured on SV-COMP and not run with the test suite yet.
8. `ite(c, 1, 0) != 0` of `assume_abort_if_not` is not simplified to `c` inside `invs`
   (array_init_nondet_vars, pair_symmetr2).
9. Reading an iteration constraint at a witness `0 <= x < n` (standard_vararg, array_init_nondet_vars,
   standard_sentinel-2).
10. `-debug match` reports nothing for rules whose left-hand side is not a trace.

## Reducer commutativity (current work, TODO.md "Work queue: Now")

reducercommutativity (avg, max, rangesum, sep, sum) and array-crafted bAnd, bor, xor: `R(x) == R(swap(x, 0, 1)) ==
R(rotate(x))` for a reduction `R` over `x[0..N)` of nondeterministic values, `N` a literal from 5 to 100000; none is
solved, sum and avg time out.

The goal of bAnd1 after `-teq -prove`, with `T` the values:

```
R1 = current(trace(T[0], for k in ⌊counter(0,1,99)⌋ :: bitand(r, earlier(k+1, T))))
R2 = current(trace(T[1], for i in ⌊counter(1,1,99)⌋ :: bitand(r, s[i])))
       s   = x21[0 := T[1]][1 := T[0]],   x21 = current(stores(x3, ⌊counter(0,1,100)⌋, T))
R3 = current(trace(x56[0], for i in ⌊counter(1,1,99)⌋ :: bitand(r, x56[99 := T[1]][i])))
       x56 = current(trace(s, for k in ⌊counter(0,1,99)⌋ :: x[k := x[k+1]]))
```

- R1 reads lists (`current_stores` evaluated the reads), R2 and R3 arrays: `s[i]` over two stores is not decided for
  `i == 1`, the shift loop is not folded. The swap fold of sorted.dfy does not apply: the reads `x[1]`, `x[0]` of the
  swap are evaluated before it matches, and where it does fold, `select_swap` evaluates its reads again.
- Plan, by rules only, no normalization in the engine: one fold per operator, as `sums` for addition (`bitands`,
  `bitors`, `bitxors`; `maxs`, `mins`; `parities` exists for sep), no higher-order step, since a step `F` would bind to
  a `Lam` and its conditions would be quantified side conditions over beta-reduced lambdas; `max` and `min` as folds of
  their conditionals, with the symmetric variants (`<` and `<=`, the mirrored comparisons, the case forms, argument
  order); per operator first-order lemmas: the exchange of the seed with an element (the swap, with the values as
  conditions `v == a[q]`, `w == a[p]`), the last element moved to the seed (the rotation, after the shift loop as
  stores that read ahead); the value lists normalized by lemmas on `maps` of `earlier` at shifted counters (a slice),
  such that R1 and R2 read the same term.
- The removed `store_occurs_selects` fired at the reads of the swapped array; on a sum over five elements after a swap
  the run ended without it (`unknown`, 19 s at a load of 13) instead of a timeout. The remaining goal is
  `sum(selects(x[0 := T[1]][1 := T[0]], ⌊K⌋))`, the shape of a swap lemma for sums (prototype in the scratch include
  of Oct 26, not run on an idle machine).

## Not addressed

- array-patterns (30 true): pairwise cancelling sums over stores at nondeterministic indices (TODO.md).
- array-tiling rewrev, rewnifrev, nr2-nr5, pnr2, pr3-pr5, mbpr3: stores at reversed and strided positions, inner
  loops of a literal number of iterations.
- array-multidimensional with three dimensions and max/min/add/diff: timeouts.
- array_monotonic, sanfoundry_10: conditional stores at a stride-2 counter, a search with two exits.
- array-fpi (17 false unknown): counterexamples (TODO.md, concrete evaluation).

## Measurements

Local runs at 90 s were disturbed by other sessions (load 13 to 17 on four cores). VerifierCloud, Oct 26, 2026
(out/bench/cuvee-arrays.xml: 120 s, one core, Ryzen 7 PRO 5750G; `base` the jar of 0.52.4, `db-lemmas` the same jar
with the edited database and `teq:arraylemmas`; results/cuvee-arrays.*), true and false correct:

| | Arrays | Arrays, fallback | Loops | Loops, fallback |
|---|---|---|---|---|
| base | 137, 62 | 159, 62 | 217, 28 | 248, 28 |
| db-lemmas | 165, 62 | 172, 62 | 218, 29 | 240, 29 |

- Arrays: the 29 tasks of the lemmas gained, standard_sentinel-2 lost (`store_occurs_selects`); with the fallback
  also sep05-1 (at the limit before). No flips, no wrong results.
- Loops: array_2-1-simple (false) and array_2-2-simple gained; loop-acceleration/array_4 lost, a sentinel search
  like standard_sentinel-2 (`store_occurs_selects`); with the fallback 10 lost, timeouts of tasks near the limit,
  mostly nla-digbench-scaling (cohencu, cohendiv, prodbin), presumably the forward lemma `div_mod` at every division.
- The runs predate `invs_select_store_ne`, which recovers the two sentinel searches (local runs, 8 s each).
- The median CPU time of the tasks solved by both rose from 22.6 s to 28.0 s (Arrays) and 21.7 s to 27.5 s (Loops).

Tests: examples/c/teq/copy_prefix.c, max_prefix.c, rows.c (unknown without the lemmas) and their `_wrong` variants
(unknown); maps_earlier_prefix.c (a wrong assertion over a prefix) stays unknown. The workarounds were
checked on programs with wrong assertions (compaction, filter, seeded maximum, both ends): unknown.
