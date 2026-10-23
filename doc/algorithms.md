# Algorithms with trace equation systems

[examples/dafny/algorithms](../examples/dafny/algorithms) holds classical array algorithms (searches, sorts,
partitions, nested loops over matrices) verified with `-teq -prove`. Each file states its command line in its first
line and its status in its header, the lemmas specific to the algorithm stand at its beginning, and `name.out`,
`name.err` are its expected outputs. The folder is not part of the default tests, since its runs take up to a minute
each: `CUVEE_ALGORITHMS=1 mill -i test` and `scripts/prove/slow.sh` run it.

## Status

Run locally with 0.50.8 on Oct 23, 2026 (90 s each, two at a time, under load); all outputs as expected, except cocktail_sort.

| example | status | time |
|---|---|---|
| [lsearch](../examples/dafny/algorithms/lsearch.dfy) | verified, database alone (`teq:search`) | 5s |
| [bsearch](../examples/dafny/algorithms/bsearch.dfy) | verified: the rule `bisection` names the trace of `(lo, hi)` | 23s |
| [lower_bound](../examples/dafny/algorithms/lower_bound.dfy) | verified, database alone (`teq:search`, `teq:sorted`): the bisection and the partition points | 55s |
| [count_occurrences](../examples/dafny/algorithms/count_occurrences.dfy) | verified: the count over the counter named as the normal form | 4s |
| [max_element](../examples/dafny/algorithms/max_element.dfy) | verified with `occurs`; the version with `exists` stays open (no witness) | 12s |
| [argmax](../examples/dafny/algorithms/argmax.dfy) | verified: the fold `argmaxs` and rules on the atoms of the postcondition | 4s |
| [is_sorted](../examples/dafny/algorithms/is_sorted.dfy) | verified, database alone: `current_trace_flag`, `sorted_adjacent` | 66s |
| [reverse](../examples/dafny/algorithms/reverse.dfy) | verified: two pointers, the summary of the swaps with the exit as side condition | 4s |
| [prefix_sums](../examples/dafny/algorithms/prefix_sums.dfy) | verified: the recurrence with the term at the written position | 7s |
| [perm](../examples/dafny/algorithms/perm.dfy) | verified, database alone (`teq:sorted`): traces of swaps | 6s |
| [inner_loop_flat](../examples/dafny/algorithms/inner_loop_flat.dfy) | verified: the facts of an inner loop at the top level | 1s |
| [nested_counter](../examples/dafny/algorithms/nested_counter.dfy) | verified, database alone | 16s |
| [nested_sum](../examples/dafny/algorithms/nested_sum.dfy) | verified, database alone | 5s |
| [nested_mult](../examples/dafny/algorithms/nested_mult.dfy) | verified, database alone | 6s |
| [row_sums](../examples/dafny/algorithms/row_sums.dfy) | verified, database alone | 7s |
| [transpose](../examples/dafny/algorithms/transpose.dfy) | verified: one summary of the nested trace | 4s |
| [invs_counter_equation](../examples/dafny/algorithms/invs_counter_equation.dfy) | verified: the facts of an inner loop inside an iteration constraint | 6s |
| [invs_fragments](../examples/dafny/algorithms/invs_fragments.dfy) | verified: fragments of an inner loop that share no facts | 38s |
| [distinct](../examples/dafny/algorithms/distinct.dfy) | verified: a flag over nested loops, its summary | 8s |
| [first_duplicate](../examples/dafny/algorithms/first_duplicate.dfy) | verified (`-prove -split -prove`): the inner scan folded, one rule per case of the flag | 7s |
| [bubble_sort](../examples/dafny/algorithms/bubble_sort.dfy) | verified: the pass folded, an induction over the passes, `perm_steps_nat` | 35s |
| [selection_sort](../examples/dafny/algorithms/selection_sort.dfy) | verified: the inner loop as a swap with `argmin`, an induction, `perm_steps_three` | 42s |
| [insertion_sort](../examples/dafny/algorithms/insertion_sort.dfy) | verified: the pass folded (position `k - kk`), an induction, `perm_steps_three` | 34s |
| [insertion_sort2](../examples/dafny/algorithms/insertion_sort2.dfy) | verified: the pass folded, the constraints of the pass as side conditions, `perm_steps_three` | 31s |
| [gnome_sort](../examples/dafny/algorithms/gnome_sort.dfy) | verified: the invariant `sorted(b, 0, i)` as one rule on the atom, open trace variables | 14s |
| [partition](../examples/dafny/algorithms/partition.dfy) | verified: Lomuto, one trace of `(b, i, j)`, the regions as rules on the atoms | 50s |
| [three_way_partition](../examples/dafny/algorithms/three_way_partition.dfy) | verified: Dutch flag, one trace of `(b, eq, j, lt)` | 66s |
| [merge](../examples/dafny/algorithms/merge.dfy) | verified: a pinned higher-order guard, pointers tied by open trace variables | 39s |
| [counting_sort](../examples/dafny/algorithms/counting_sort.dfy) | open: "rewriting does not terminate" (lemmas of the per-variable form) | 36s |
| [cocktail_sort](../examples/dafny/algorithms/cocktail_sort.dfy) | open: no answer within 90 s, formerly "rewriting does not terminate" (lemmas of the per-variable form) | 90s |

## How they are proved

`-teq` gives each strongly connected component of the variables of a loop one trace, and an inner loop is a value
of the outer update ([teq.md](teq.md)), so nested loops need no lemmas of their own: nested_counter, nested_sum,
nested_mult, row_sums and transpose prove with the database alone (transpose with one summary of its nested trace).
The others combine the database with local lemmas of a few kinds:

- **Abstract predicates** for the postconditions: `sorted`, `perm`, `partitioned` and the swap `swap(a, p, q)` of
  `teq:sorted`, which the sorts include; local ones where the database has none (`bubbled`, `shaken`, `nodup`,
  `merged`, `rank_table`, `keys_below`), declared without a body, i.e. characterized only by the lemmas.
- **Folds of inner loops** (`bubble_pass`, `insert_pass`, `lomuto`, `threeway`, `scan`, `column`, `argmaxs`): the
  trace of a pass becomes a function application, about which the lemmas speak.
- **Inductions** over the outer trace with the invariant indexed by the iteration and a quantified side condition,
  `forall b, k :: 0 <= k < m && I(b, k) ==> I(F(b, k), k + 1)`, which `-prove` decides by step lemmas on the atoms
  (`sorted_prefix_steps` of `teq:sorted`, `sorted_bubbled_steps_choice`, `sorted_insert_steps`); all steps must be
  constrained, so the number of steps is fixed exactly or the invariant clamped.
- **Rules on the atoms of the postcondition** for named results, with the range as a side condition, e.g.
  `(a[k] <= a[current(argmaxs(...))]) <==> true` (argmax, the inner loop of selection sort), the regions of a
  partition over the whole trace of `(b, i, j)` (partition, three_way_partition).
- **Named traces of cycles**: the binary searches (bsearch, lower_bound) name the trace of `(lo, hi)` by
  `bisection` of `teq:search`, whose bounds are cuts (doc/prove.md).

## Writing lemmas for an algorithm

What the work on these examples taught, as far as it holds for `-prove` (the database's own conventions are in
[teq.md](teq.md)):

1. **Name the normal form.** A counter is not inlined into the facts, so `count(x, selects(a, ⌊I⌋))` and the same
   over `⌊counter(0, 1, n)⌋` differ; a lemma that names the term over the counter makes both sides equal.
2. **Variables named apart** from those of the method and of the database rules (`ar`, `len`, `y` for `a`, `n`, `x`):
   a lemma variable with the name of a goal variable captures it.
3. **Include only the modules the lemmas are written for.** A module's other rules are tried as well; the sorts
   include `teq:sorted` instead of copying its predicates (30 to 80 % slower, but the same results), merge,
   cocktail_sort, three_way_partition and counting_sort still copy them, since they time out either way.
4. **Swaps as `swap(...)`** in the lemmas of programs that include `teq:sorted`: the stores of the program are folded
   before they are matched, so a lemma that spells out the two stores no longer matches.
5. **Two pointers instead of index arithmetic.** `b[n - 1 - i]` is arithmetic on a bound variable, which a pattern
   does not match; a second pointer counting down is a counter (reverse.dfy); a literal `-1` in a pattern is not
   matched either, so the step is a variable with a side condition.
6. **Pins for literal patterns** that the matcher does not handle: a higher-order guard `G(i, j)` fixed by a side
   condition `forall i, j :: G(i, j) <==> ...` (merge.dfy, insertion_sort.dfy).
7. **Open trace variables** tie a dependency to its trace: `Iv == trace(...)` matched against the hypothesis, then
   `is == ⌊Iv⌋` (merge.dfy, counting_sort.dfy, gnome_sort.dfy).
8. **Atoms for quantified hypotheses**, e.g. `keys_below(a, n, k)` for `forall i :: 0 <= i < n ==> 0 <= a[i] < k`,
   since a quantified side condition is not matched against a quantified hypothesis.
9. **Existential postconditions have no witness**: `exists k :: a[k] == m` stays open (max_element.dfy); the same
   statement as `occurs(m, selects(...))` in the vocabulary of the database is closed.

## Open

- cocktail_sort and counting_sort end with "rewriting does not terminate"; their lemmas were written for the former
  per-variable form and do not match the closed nested loops of `-teq`.
- max_element with `exists` (no witness).
- The algorithms that still copy the predicates of `teq:sorted` (rule 3 above).
- The matcher gaps that the lemmas work around are listed in TODO.md ("Simplifier and rewriting", found under the
  former `-simplify`, to be rechecked under `-prove`) and in [ideas/database-review.md](../ideas/database-review.md)
  (the lemmas that work around gaps of the engine).

## History

The examples were developed from Oct 9 to Oct 16, 2026 under the former `-simplify` with one trace per variable:
nested loops then needed fragment lemmas (the module `nested`, fragments.dfy, both removed on Oct 23), and the work
produced 37 numbered findings about the tool and proposals, recorded in the former NOTES.md of the folder (its last
version: `git show 1318322c:examples/dafny/algorithms/NOTES.md`; the findings that references in bugs.md and the
examples cite by number are there). The write-up of that period is [array-algorithms](array-algorithms). On Oct 23
the duplicates of examples/dafny/state replaced their versions here with the database alone, and the local copies of
database lemmas went (doc of the database review: [ideas/database-review.md](../ideas/database-review.md)).
