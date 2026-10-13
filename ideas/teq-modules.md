# The lemma database after the switch to the state form: a reorganization of the modules

Oct 13, 2026, after `-teq` partitioned every loop by its components (0.46.0). A proposal, being implemented file by
file; the user agreed to the plan, with an example per lemma only where intuition asks for one, and with the usage
statistics of the experiments (scripts/out/rules.csv, rules-unused.txt) as a guide.

**Progress.**
- `core.dfy` migrated (Oct 13): teq.dfy declares `distincts`, `parity`, `max`, `min`, `count`, `pow` as well, the file
  is in `legacy/`; count_occurrences, distinct, first_duplicate, merge and fallback_recursion run again (with goals),
  counting_sort does not terminate under `-prove` now that `count` resolves (its own lemmas).
- `aggregation.dfy` migrated (Oct 13), 53 to 31 declarations: the sums and their lemmas left to teq.dfy, the rules
  never applied on SV-COMP and specific to one task left in legacy/teq.dfy (below_prefix, nonneg_prefix, parities,
  the maxima and minima of counters and constants, the prefixes of maxima, minima and counts, the indicators of two
  dependencies, the updates of selects, sum_squares); `count_nonnegative`, `current_maxs_initial`,
  `current_mins_initial` forward lemmas. 14 examples include it now (before `teq:nested`, which needs
  `consts_prefix`): invs_counter_equation, invs_fragments, nested_mult, row_sums and include_before_teq close, the
  other nine run with goals, count_occurrences with one goal fewer; cocktail_sort does not terminate (deferred, the
  user remembers it as tricky).
- `arithmetic.dfy` migrated (Oct 13), 30 to 10 rules, cross-checked against `-prove` with each rule stated as a goal:
  `-prove` decides mod_add_even, the halves and thirds of polynomials with literal coefficients, natural_zero and
  integer_zero on its own, five rules on naturals are in teq.dfy, natural_one/two and integer_one/two and
  div_quotient_remainder were never applied on SV-COMP (the latter does not match the product `k * m` of the normal
  form, TODO.md); the bounds of the triangles are forward lemmas, which makes their sums with a nonnegative `d`
  follow by the simplex, so those two rules are gone. A goal that is a bare atom needs the forward lemmas to fire
  when the atom is decided, which `-prove` does now for comparisons and equations at positions with a polarity
  (`Simplify.forward`). No example changes with the module; the benchmark definitions include both migrated modules.
- Regrouped (Oct 13, the user's wish): `sum`, `count`, `max`, `min`, `parity` and the sums with their lemmas moved
  from teq.dfy into aggregation.dfy, `parities` back from legacy; `pow` into arithmetic.dfy. Eleven examples that
  used them include `teq:aggregation` now (fallback_recursion also `teq:arithmetic`), with unchanged results except
  counting_sort, which does not terminate on another rule now.
- `search.dfy`, `sorting.dfy` (now `sorted.dfy`), `arrays.dfy`, `counters.dfy`, `strides.dfy` migrated (Oct 13):
  search with the lsearch rules of teq.dfy and the bisection of examples/dafny/state (`bisection`, `bisection_lo/hi`),
  its facts at the reads (`earlier_agree_prefix`, `earlier_not_occurs_prefix`, `select_not_occurs_selects`,
  `earlier_above_iterations`) forward lemmas; sorted with the partition points (`lower`, `upper`, `bounds`,
  `cut_lower`, `lower_succ`) over `sorted(a, 0, n)`, so bsearch_bisect, bsearch_safe and lower_bound of
  examples/dafny/state include `teq:search` and `teq:sorted` instead of declaring them; arrays 24 to 10 rules (the
  recurrences with sums in aggregation); counters 60 to 9 rules on the shapes of traces over a counter, the bounds of
  iteration constraints (`invs_const`, `invs_counter_lower`, `invs_counter_upper_nonnegative` before
  `invs_counter_upper`, which loops otherwise) and `distincts_counter` in teq.dfy, `mods` left in the legacy file
  (the C examples close without it under `-prove`); strides unchanged. In teq.dfy, `zero_integer` is oriented
  `(integer(n) == 0) <==> (n == zero)` with the forward lemma `zero_integer_value`, since the other orientation looped
  with `integer_eq`. In `-prove`: a forward instance that simplifies to true is assumed as it is (its atoms are what
  the classes need), and conclusions that `-split` turned into `... ==> false` are taken apart (`Forward.from`). Of the
  algorithms, perm, lower_bound and affine close now, is_sorted, reverse, lsearch, nested_* and others have fewer
  goals; bubble_sort, insertion_sort and insertion_sort2 loop with `teq:sorted` and without `teq:nested`, so they keep
  `teq:nested`; cocktail_sort and counting_sort do not terminate (deferred).
- Next: retiring nested (a rewrite of the lemmas of the three sorts), the remaining conversions to forward lemmas,
  the firing at definitions (step 3 of J) before more forward lemmas.

## The state of the files (before the migration)

| file | functions | rules | written for | state |
|---|---|---|---|---|
| `teq.dfy` (entry, injected by `-teq`) | 15 + 3 types | 35 `{:rw}` | the state form (the former `state.dfy`) | injected |
| `teq/core.dfy` | 19 + 3 types | none | per-variable | duplicates 16 declarations of `teq.dfy`, adds `count`, `distincts`, `max`, `min`, `parity`, `pow`; cannot be included with `teq.dfy` |
| `teq/arithmetic.dfy` | 0 | 30 | both (no traces) | needs `core.dfy` only for `Nat` |
| `teq/counters.dfy` | `mods` | 60 (16 on `invs`) | per-variable | partly duplicated in `teq.dfy` (counter, consts) |
| `teq/aggregation.dfy` | `sums`, `counts`, `maxs`, `mins`, `parities`, `consts_prefix`, `below_prefix`, `nonneg_prefix` | 51 | per-variable | `sums` duplicated in `teq.dfy` |
| `teq/arrays.dfy` | `stores`, `shifts` | 24 | per-variable | `stores` duplicated in `teq.dfy` |
| `teq/search.dfy` | `agree_prefix`, `above_iterations` | 9 | per-variable | `select_not_occurs_selects` duplicated in `teq.dfy` |
| `teq/nested.dfy` | `results` | 11 (7 on `invs` of fragments) | per-variable only | needs `consts_prefix` of aggregation |
| `teq/sorting.dfy` | `sorted`, `perm`, `partitioned` | 13 | both | now `teq/sorted.dfy` |
| `teq/strides.dfy` | none | 5 | per-variable (MonoCera) | untested |
| `legacy/teq.dfy` | 31 | 162 | per-variable | backup, not injected |

Uses: `-include teq:nested` 25 times (algorithms), `teq:sorting` 6, `teq:strides` 6 (benchmarks), `teq:core` and
`teq:arithmetic` once. Since the switch, 14 algorithms and four Dafny examples fail on declarations that only the
old modules have: `count` (counting_sort, count_occurrences, merge, partition, three_way_partition), `distincts`
(distinct, first_duplicate), `maxs` (max_element), and `consts_prefix` of every inclusion of `teq:nested`.

What no longer applies in the state form:
- **The fragments of inner loops** (`teq:nested`, the `invs` rules over `ks, Js, Ns` and `results`): an inner loop is a
  value of the outer update, closed by substitution (examples/dafny/state: nested_sum, nested_mult, nested_counter,
  row_sums, transpose without fragment lemmas).
- **Rules over several per-variable traces of one loop** (`invs_two_phases` over a counter and a second trace, the
  `invs` rules with dependencies `hs, gs, fs` in counters.dfy): a cycle is one trace now, read by its components or
  matched as a whole (the bisection).
- **Arithmetic that the simplex decides**: division by a literal is bounded in `Linear` (`div_below` for a literal
  divisor).

## Proposal

**`teq.dfy`, always injected, is the only module that declares the core.** It takes the declarations of `core.dfy` that
it lacks (`count`, `distincts`, `max`, `min`, `parity`, `pow`) as declarations, so that every optional module refers
to `teq.dfy` only, and the rules that every loop needs: naturals and integers, counters with their reads and the
bounds of their iteration constraints (`invs_counter_lower`, `invs_counter_upper`, `invs_counter_ne_up/down`,
`invs_const` from counters.dfy), constant traces, sums, stores and selects. `core.dfy` is then dissolved.

**The optional modules by concept, each over `teq.dfy` alone**, in the order of the options:

| module | contents | from |
|---|---|---|
| `teq:arithmetic` | non-linear arithmetic: powers, triangles, parity | arithmetic.dfy, without what the simplex decides |
| `teq:aggregation` | counts, maxima, minima, parities, the prefix predicates (`consts_prefix`, `below_prefix`, `nonneg_prefix`) | aggregation.dfy, without sums |
| `teq:arrays` | shifts and the further forms of stores and selects | arrays.dfy |
| `teq:unsigned` | `mods`, the counters of the unsigned variables of C | counters.dfy (`mods_def`, `invs_mods_*`) |
| `teq:search` | linear searches (`agree_prefix`, `above_iterations`, not occurs) and the bisection (`bisection`, `cut`, `bisection_lo/hi`) | search.dfy, examples/dafny/state/bsearch_bisect.dfy |
| `teq:sorted` | sortedness, permutations, partitions, and the partition points of a sorted array (`lower`, `upper`, `equal`, `bounds`, `cut_lower`, `lower_succ`) | sorting.dfy, bsearch_bisect.dfy |
| `teq:strides` | the strided stores of MonoCera | strides.dfy, to be tested in the state form |

`teq:nested` and the fragment rules of counters.dfy are retired to `legacy/`. The modules move lemma by lemma, each
with a state-form example that uses it (the algorithms are the tests), and with its proof in Lean (`lean/`, once the module joins the stable ones); what is not
moved stays in `legacy/teq.dfy`. First step: the shared declarations into `teq.dfy`, which turns the 14 failures into
runs with goals; then search and sorted (their examples exist), aggregation (the counting algorithms), then the
rest.

## Rewrite rules or forward lemmas

A rewrite rule (`{:rw}`) applies where its left-hand side occurs; a forward lemma (`{:fw}`) is assumed wherever a
term matching its trigger occurs in an assumed fact. The choice per kind of lemma:

- **Rewrite rules**: trace introductions and folds (`trace(...) == stores(...)`, `bisection`), which name a trace;
  equations that compute a value (`current(counter(i, c, n)) == ...`, `earlier(j, ⌊sums(...)⌋) == ...`); atoms that
  occur in goals as they are, e.g. postconditions (`sorted_short`, `perm_refl`, `sorted_prefix_steps` on
  `sorted(current(...), 0, n)`); the rules on `invs` atoms of iteration constraints.
- **Forward lemmas**: facts about a term whose atom rarely occurs literally but which the arithmetic or the classes
  need where the term occurs:
  - bounds of a trace: `current_trace_bounded` (`lo <= current(trace(...)) <= hi`, a rewrite rule on the conjunction
    today, which fires only if the goal states exactly that), like `bisection_lo/hi`;
  - bounds and (dis)equations at reads: `earlier_above_iterations` (`integer(j) < earlier(j, ts)`),
    `earlier_agree_prefix` (`earlier(j, xs) == earlier(j, ys)`, an equation for the classes),
    `earlier_not_occurs_prefix` and `select_not_occurs_selects` (`earlier(j, xs) != e`, `a[k] != x`), which today
    are rules on `... <==> true/false` and fire only if that comparison is in the goal; as forward facts at
    `earlier(j, xs)` and `a[k]` they are step 2 of J;
  - the bounds of named values, like `bounds` of the partition points.
- **Both**, as a rule on the atom and a forward lemma on the term (`lower_bound` and `bounds` of
  bsearch_sorted.dfy), only where an example shows that the atom must be decided where no fact was assumed, e.g. a
  side condition decided inside an update; otherwise the forward fact suffices, since closed conditions are looked
  up among the facts.

Two cautions from the binary search:
- **Trigger on named terms, not on raw trace patterns.** A trigger that is a trace pattern is matched through the
  views at every occurrence of `⌊S⌋.i` or `current(S).i`, in every sibling context; the bisection names the trace by a
  rule and puts the forward lemmas on `current(bisection(...)).i`, which is cheap. So each forward lemma about a
  trace comes with a rule that names the trace.
- **Step 3 of J (firing at definitions, a memo per lemma and canonical term) before many forward lemmas.** The
  firing at every assumed fact is quadratic in the conjuncts of a premise; with a handful of forward lemmas it does
  not show, with dozens it will.

The conversions are made with the move into the new modules, lemma by lemma, each with the example that shows the
difference.
