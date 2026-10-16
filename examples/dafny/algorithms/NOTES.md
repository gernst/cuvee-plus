# Algorithms with trace equation systems

Experiments towards sorting and other array algorithms with nested loops with
`-teq -simplify` in the former per-variable form (until Oct 13, 2026; since then their command lines run `-teq
-prove`, one trace per strongly connected component, with the database `teq.dfy`; on Oct 16, 27 of the 30 are verified
that way, all except max_element with `exists`, cocktail_sort, and counting_sort; the rows dated Oct 16 below describe
the current lemmas, the others those of the former form), in the dialect of Dafny of Cuvée: arrays are total maps `array<int, int>`, the first `n`
elements are sorted. Each file states its command line in its first line and
its status in its header; the lemma database `teq.dfy` is injected by `-teq`,
the lemmas specific to the examples stand at the beginning of each file.

| file | status |
| ---- | ------ |
| [lsearch.dfy](lsearch.dfy) | verified (`-teq -split -simplify`) |
| [perm.dfy](perm.dfy) | verified: permutations by swaps in single loops |
| [bubble_sort.dfy](bubble_sort.dfy) | verified: nested loops, `sorted` by the induction lemma, `perm` |
| [selection_sort.dfy](selection_sort.dfy) | verified: summary of the inner loop, `sorted` by the induction lemma, `perm` |
| [insertion_sort.dfy](insertion_sort.dfy) | verified with `-prove` (Oct 16): the pass folded with the position `j - 1` as `k - kk`, the lemmas of insertion_sort2 |
| [insertion_sort2.dfy](insertion_sort2.dfy) | verified with `-prove` (Oct 16): the pass folded, an induction over the outer trace with the constraints of the pass as side conditions |
| [nested_counter.dfy](nested_counter.dfy) | verified: the simplest nested loop |
| [nested_sum.dfy](nested_sum.dfy), [nested_mult.dfy](nested_mult.dfy) | verified: the generic fragment lemmas |
| [fragments.dfy](fragments.dfy) | verified: the generic fragment lemmas on the two minimal problems |
| [inner_loop_flat.dfy](inner_loop_flat.dfy) | verified: the facts of an inner loop at the top level |
| [invs_counter_equation.dfy](invs_counter_equation.dfy) | verified with `-include teq:nested` (problem 1, minimal) |
| [invs_fragments.dfy](invs_fragments.dfy) | verified with `-include teq:nested` (problem 2, minimal); method variables named apart |
| [count_occurrences.dfy](count_occurrences.dfy) | verified: the count named as the normal form |
| [max_element.dfy](max_element.dfy) | verified with `occurs`; open with `exists` (no witness) |
| [argmax.dfy](argmax.dfy) | verified: a selection trace with rules on the atoms |
| [partition.dfy](partition.dfy) | verified with `-prove` (Oct 16): Lomuto partition, one trace of `(b, i, j)`, the regions as rules on the atoms over the whole trace |
| [reverse.dfy](reverse.dfy) | verified with `-prove` (Oct 16): two pointers, the summary takes the disjunction of the exit as its side condition |
| [is_sorted.dfy](is_sorted.dfy) | open by one substitution of the exit into `sorted`; two rules tried without effect (finding 35) |
| [row_sums.dfy](row_sums.dfy) | verified with `-include teq:nested`: a chain of specific lemmas, no substitution lemma (finding 29) |
| [transpose.dfy](transpose.dfy) | verified with `-prove` (Oct 16): the columns folded, the numbers of inner iterations fixed by `consts` |
| [prefix_sums.dfy](prefix_sums.dfy) | verified: the recurrence with the term at the written position |
| [distinct.dfy](distinct.dfy) | verified: nested loops with a flag, summary and `current_trace_all` |
| [three_way_partition.dfy](three_way_partition.dfy) | verified with `-prove` (Oct 16): Dutch flag by a single scan, one trace of `(b, eq, j, lt)`, as partition |
| [cocktail_sort.dfy](cocktail_sort.dfy) | open under `-prove` (rewriting does not terminate); verified before with `-include teq:nested`: a closed condition over fresh variables, the bound in the goal's form (finding 27) |
| [first_duplicate.dfy](first_duplicate.dfy) | verified with `-prove -split -prove` (Oct 16): the inner loop folded, one rule per case of the flag |
| [merge.dfy](merge.dfy) | verified: pinned higher-order guard, pointers tied by open trace variables |
| [counting_sort.dfy](counting_sort.dfy) | open under `-prove` (rewriting does not terminate); verified before: four loops in sequence, the key range as an atom |
| [lower_bound.dfy](lower_bound.dfy) | open: closes only with the exit untied from the traces; sound ties re-enter (finding 32); verified under `-prove` by a bisection lemma over the cycle ([state/lower_bound.dfy](../state/lower_bound.dfy)) |
| [gnome_sort.dfy](gnome_sort.dfy) | verified: the invariant `sorted(b, 0, i)` in one lemma on the atom, the traces tied by open trace variables (finding 36) |

## Abstract predicates

- `sorted(a, lo, hi)`: `a[lo..hi)` is nondecreasing.
- `perm(a, b)`: `a` is a permutation of `b`, as total maps on the indices,
  i.e. `a` is `b` composed with a bijection of the indices. Whole arrays, so
  that no side conditions on the ranges of the swapped positions are needed:
  a swap at any two positions preserves it. Planned: `partitioned(a, lo, mid, hi)`,
  all of `a[lo..mid)` are at most all of `a[mid..hi)`, for the pass facts below.
- Lemmas on `perm`: `perm(a, a)`; a swap `a[p := a[q]][q := a[p]]` on the
  left preserves `perm(_, b)`; a trace of swaps at positions `P(x, k, h)`,
  `Q(x, k, h)` that depend on the state and the iteration preserves it (a
  higher-order pattern); a trace of steps `F(b, k)` preserves it if
  `forall b, k :: perm(F(b, k), b)`, a quantified side condition that the
  simplifier decides once `F` is instantiated (`perm_steps`,
  bubble_sort.dfy).

## What `-teq` does with nested loops

The inner loop is summarized during the symbolic execution of the outer body
(theorem 4.8 of the paper). Its trace equation system is in terms of fresh
variables (its counter `K'`, its number of iterations `n'`, its traces `J`,
`B'`, and the final values `j`, `b'`), which become fresh *sequences*
`K?`, `N?`, `J?`, `B?`, ... over the outer iterations, i.e. dependencies of
the outer combinators. The outer trace of a variable that only the inner loop
modifies is the chain of the inner results,
`B == trace(a, for ⌊K⌋, B? do b, k, b' :: b')`, named `results(a, ⌊K⌋, B?)`
in the examples. The inner trace equation system becomes part of the body of
the iteration constraint of the outer loop:

```
invs(for ⌊K⌋, ⌊I⌋, ⌊B⌋, B?, J?, N?, K?, B?', J?' check k, i, b, b', j, n', K', B', J' ::
  1 < i && K' == counter(0, 1, n') && b' == current(B') && j == current(J')
  && B' == trace(b, for ⌊K'⌋, ⌊J'⌋ do x, k', j' :: case ... => swap case ... => x)
  && J' == trace(0, for ⌊K'⌋, ⌊B'⌋ do j', k', x :: j' + 1)
  && invs(for ⌊K'⌋, ... check ... :: j' + 1 < i) && 0 <= integer(n') && !(j + 1 < i) && ...)
```

The simplifier distributes this `invs` over its conjuncts, each with the
dependencies it uses (doc/teq.md), and in the examples the result is a dozen
fragments:

```
invs(for ⌊K⌋, ⌊I⌋, N?, K? check k, i, n', K' :: K' == counter(0, 1, n'))
invs(for ⌊K⌋, ⌊I⌋, B?, B?' check k, i, b', B' :: b' == current(B'))
invs(for ⌊K⌋, ⌊B⌋, ⌊I⌋, B?', J?' check k, b, i, B', J' :: B' == bubble_pass(b, ⌊J'⌋))
invs(for ⌊K⌋, ⌊I⌋, K?, J?' check k, i, K', J' :: J' == sums(0, maps(for ⌊K'⌋ yield k' :: 1)))
invs(for ⌊K⌋, ⌊I⌋, J?' check k, i, J' :: invs(for ⌊J'⌋ check j' :: j' + k + 1 < n))
invs(for ⌊K⌋, ⌊I⌋, J? check k, i, j :: n <= j + k + 1)
...
```

## The two problems of nested loops

Both are in the simplifier and are isolated in two small files, whose goals
are written by hand (`assume`/`assert` in a method). The same facts at the top
level, without sequences, are proved (inner_loop_flat.dfy): `j == n` follows
from `K' == counter(0, 1, n')`, `J' == trace(0, for ⌊K'⌋ do x, i :: x + 1)`,
`j == current(J')`, the iteration constraint `x < n`, and the exit `!(j < n)`.

1. **The equation of a bound variable is not followed in the body of a
   combinator** (invs_counter_equation.dfy). Inside the `invs`,
   `J' == trace(0, for ⌊K'⌋ do x, i :: x + 1)` is not rewritten by
   `counter_def` through the sibling conjunct `K' == counter(0, 1, n')`
   (`Ctx.↑` does this at the top level), so the generic fold of `sums`
   applies instead and `J' == sums(0, maps(for ⌊K'⌋ yield i :: 1))` remains,
   which no lemma recognizes as a counter. With the counter inlined,
   `J' == trace(0, for ⌊counter(0, 1, n')⌋ ...)`, it is a counter and the
   inner iteration constraint resolves to `n' == zero || ... <= n`
   (invs_fragments.dfy). Presumably the bound variables are bound to
   `earlier(natural(k), Z)` by `Simplify.iterations` and the equations of the
   body are not recorded for `↑`; a remedy is to record the equations
   `z == e` of the body for the bound variables `z` before the siblings are
   simplified (as `nary` assumes the other conjuncts).

2. **Fragments do not share facts** (invs_fragments.dfy). The body of an
   `invs` assumes only the invariants whose dependencies are among its own
   (`Simplify.invariants`). The fragments of an inner loop have
   incomparable dependencies (`N?, J?'` vs `J?', J?` vs `J?`), so
   `j == current(J')` is not rewritten to `j == integer(n')` although
   `J' == counter(0, 1, n')` holds at the same position. All fragments range
   over the same counter `⌊K⌋`, hence the facts of one hold at position `k`
   of another with its other dependencies instantiated by
   `earlier(natural(k), Z)` (the fallback of the paper, (†)); a remedy is
   that the body of a combinator over `⌊K⌋` assumes the bodies of all
   `invs` over `⌊K⌋`, with the bound variables of dependencies not shared
   replaced by `earlier(natural(k), Z)`. Alternatively, the trace equation
   system of the inner loop could be simplified as a unit when it is
   summarized, before it becomes sequences (the facts of one iteration,
   as in inner_loop_flat.dfy, are enough to derive `j == n`).

With both, nested_sum.dfy would need `J? == ⌊consts(m, n)⌋` from
`invs(for ⌊counter(0, 1, m)⌋, J? check k, j :: j == n)` (a lemma to add) and
`sum_consts`; nested_mult.dfy would need `R == counter(0, n, m)` from the
chain of the inner sums; and the sorting algorithms would get the summary of
the inner loop directly, e.g.
`B == trace(a, for ⌊K⌋ do b, k :: current(bubble_pass(b, ⌊counter(0, 1, n - k - 1)⌋)))`,
instead of the lemma `current_results_bubble` below.

## Update (Oct 9, 2026, evening): sharing of facts implemented

`Simplify.invariants` now assumes, in the body of a combinator over the
counter `⌊K⌋`, all `invs` over the same counter, with unshared dependencies
instantiated pointwise by `earlier(natural(k), Z)`; a shared equation that
eliminates the bound variables, e.g. `integer(earlier(natural(k), N?)) == n`,
becomes a rewrite rule of the context (`Simplify.combinator`,
`Context.rule`), since its arithmetic solution would be for `n`. Three
lemmas were added to teq.dfy: `sums_consts`, `invs_counter_upper_nonnegative`,
and `sum_invs_const`. With these, invs_fragments.dfy is closed, and in
nested_sum.dfy the inner loop is summarized to `j == n` per iteration and
the sum lemma fires; `integer(n') * n == m * n` with `integer(n') == m`
remains at the top level. In nested_mult.dfy the fragment of the inner
result is `r' == earlier(natural(k), ⌊R⌋) + n`, where the accumulator of
`R == trace(0, for ⌊K⌋, R? do r, k, r' :: r')` is not related to
`earlier(natural(k), ⌊R⌋)` (an experiment with a map of such terms in
`Chains`, looked up by `↑` like variables, was dropped). bubble_sort.dfy
no longer closes, since its summary lemma matches the former shape of the
fragments; it should be dropped once the summary comes from the tool.
Problem 1 above (the equation of a bound variable in the same body) remains
in invs_counter_equation.dfy.

## Principles from further standard algorithms (Oct 9, 2026, late)

Single-loop algorithms over arrays, each with its local lemmas: count_occurrences.dfy,
max_element.dfy, argmax.dfy, partition.dfy (Lomuto), reverse.dfy are verified;
is_sorted.dfy is open by one substitution. What each needed:

1. **Name the normal form.** The counter `I` of a loop is not inlined into the
   facts, so `count(x, selects(a, ⌊I⌋))` and `count(x, selects(a, ⌊counter(0, 1, n)⌋))`
   of the postcondition differ. A lemma that names the count over a counter
   makes both sides the same term. The same for the count of elements below
   the pivot in partition.dfy, where the side conditions of the lemmas and the
   facts of the goal differ in the names of the bound variables of the maps,
   which are compared literally.
2. **Facts of a named trace as rules on the atoms of the postcondition.** A
   selection trace (argmax, the inner loop of selection sort) is named, and
   its current value is characterized by rules `(a[k] <= a[current(argmaxs(...))]) <==> true`
   with the range of `k` as a side condition, and by rules for its bounds.
   The partition is the same with `below`/`above` rules, plus `perm`.
3. **Join the cases that the postcondition does not split.** `a[k] <= m` for
   the maximum needs `current_maxs_initial` for `k == 0` and
   `current_maxs_earlier` for the rest; the simplifier does not split `k`, so
   one lemma with the disjunction `k == j || i <= k < i + n` as side condition.
4. **Existential postconditions have no witness.** `exists k :: a[k] == m` is
   not closed: a rule whose left-hand side is a quantifier is not matched, and
   `-teq` produces no witness. The postcondition `occurs(m, selects(a, ⌊counter(...)⌋))`
   in the vocabulary of the database is closed by a lemma on `occurs`.
5. **Flags are iteration constraints.** `current_trace_flag` turns the flag of
   is_sorted.dfy into `if invs(...) then true else false`, and the constraint
   over adjacent positions is the abstract predicate by its definition lemma.
   The lemma of teq.dfy is typed `int`; a polymorphic version is needed.
6. **Reads of the position of the iteration are reads of the input** when
   only positions below it are written before (partition.dfy), stated on the
   map that reads them with the named trace as a dependency. A lemma that
   rewrites the read inside the trace itself does not terminate, since it
   applies again in the update of its own instance.
7. **Lemmas carry the extra dependencies** that the simplifier keeps in maps
   (the counter of the loop as `hs`), otherwise their side conditions do not
   match the facts.
8. **Two pointers instead of index arithmetic.** `b[n - 1 - i]` in an update
   is arithmetic on a bound variable, which patterns do not match; the second
   pointer `j` is a counter down, and the lemma on the trace of swaps matches
   `⌊counter(c, d, n)⌋` with `d == -1` as a side condition, since the literal
   `-1` in a pattern is not matched.
9. **Closed `invs` side conditions fail.** The simplifier drops the unused
   dependencies of the instance, which makes it closed, and a closed `invs` is
   decided literally against the facts (see bubble_sort.dfy); iteration
   constraints that teq.dfy does not resolve, e.g. `2 k + 1 < n`, need a lemma
   to arithmetic (`invs_pairs`), and the exit over a definition `i == integer(n)`
   needs a rewrite of the exit atom (`exit_pointers`), since definitions by
   non-arithmetic terms are followed on demand only, not substituted.
10. **Degenerate iteration counts need `-split` after `-simplify`.** The exit
    of a loop is a disjunction with the case of no iteration, which appears
    only after the first simplification; the pipeline `-teq -simplify -split -simplify`
    separates it (is_sorted.dfy, reverse.dfy).
11. **Open in the simplifier:** a solution `n == n' + 1` of the exit is not
    substituted into `sorted(a, 0, n)` (a bare variable as an argument is not
    replaced), which is all that remains of is_sorted.dfy; equalities of reads
    `a[k] == a[m]` whose indices are equal by linear arithmetic with
    coefficients are beyond the difference constraints.

## How bubble_sort.dfy is verified nevertheless

The summary of the inner loop is a lemma whose side conditions are the
fragments, matched against the facts of the goal (`Rewrite.conditions`),
which binds the sequences:

```
lemma {:rw} current_results_bubble(a, len, ks, js, Js, ..., bs, Bs)
  requires invs(for ks, bs, Bs check k, b, B :: b == current(B))
  requires invs(for ks, ⌊results(a, ks, bs)⌋, Bs, Js check k, x, B, J :: B == bubble_pass(x, ⌊J⌋))
  requires invs(for ks, js check k, j :: len <= j + k + 1)                            // binds len
  requires invs(for ks, Js2 check k, J :: invs(for ⌊J⌋ check j :: j + k + 1 < len))
  requires Js2 == Js
  requires invs(for ks, js3, Js3 check k, j, J :: j == current(J))
  requires js3 == js && Js3 == Js
  requires invs(for ks, Ks, Js check k, K, J :: J == sums(0, maps(for ⌊K⌋ yield k2 :: 1)))
  ensures current(results(a, ks, bs))
    == current(trace(a, for ks do b, k :: current(bubble_pass(b, ⌊counter(0, 1, natural(passlen(len, k)))⌋))))
```

Then `perm_steps` (generic) and `sorted_bubble_passes` (bubble sort sorts:
`n` passes, the `k`-th over `0, ..., len - k - 2`, sort `0, ..., len - 1` if
`len <= n + 1`) close the goal; `-split` is not needed. Findings about the
matching, each a workaround in the lemma and a candidate for the tool:

- A rule whose left-hand side is `results(a, ks, bs)` does not terminate: it
  is tried again on the `results` inside its own side condition when the
  instance is simplified. Hence the left-hand side is `current(results(...))`.
- `⌊counter(0, 1, n)⌋` as an argument of the left-hand side
  (`results(a, ⌊counter(0, 1, n)⌋, bs)`) does not match `⌊K⌋` with
  `K == counter(0, 1, n')` in the context; as a dependency of a combinator it
  does (bsearch.dfy). Hence `ks` is generic, and the lemma is sound for any
  `ks`.
- An `invs` side condition is matched against the facts only while one of
  its sequence variables is open. A closed instance is decided by the
  simplifier, which does not find it among the facts: these keep the counter
  `⌊I⌋` as an unused dependency and the instance's bound variables are
  renamed. Hence the order of the conditions, each binding a new sequence,
  and the duplicates `Js2`, `js3`, `Js3`, identified by equations, which are
  closed and decided trivially. (`conditions` backtracks over the facts, so a
  condition of the same shape as another fact, e.g. `t == current(T)` of the
  temporary `t`, is harmless.)
- A pattern with arithmetic on a bound variable of a combinator,
  `natural(len - k - 1)`, is not matched (TODO.md), hence the function
  `passlen(len, k)` without a rewrite rule.
- The fold of a swap `x[j := x[j - 1]][j - 1 := x[j]]` (insertion_sort.dfy)
  does not match for the same reason; higher-order positions `P(y, j)`,
  `Q(y, j)` do.

## Towards a database of sorting lemmas

`sorted_bubble_passes` states the correctness of the whole outer loop, like
`current_trace_two_phases` or `current_trace_catch_up` of teq.dfy state the
result of a loop shape. A more compositional set, to be tried once the
summary of inner loops is available from the tool:

- facts about one pass `p = current(bubble_pass(b, ⌊counter(0, 1, natural(m))⌋))`
  for `0 <= m`: `perm(p, b)`; `p[j] == b[j]` for `m < j`;
  `sorted(p, m, hi) <==> sorted(b, m + 1, hi) && partitioned(b, 0, m + 1, hi)`
  (the maximum of `b[0..m]` moves to `m`);
  `partitioned(p, 0, m, hi) <==> partitioned(b, 0, m + 1, hi)`;
- a generic induction over a trace of steps `F(b, k)` with the invariant
  `sorted(b, len - k, len) && partitioned(b, 0, len - k, len)`, whose
  quantified side condition the simplifier decides by the pass facts, as it
  decides that of `perm_steps`;
- selection sort: the inner loop is the position of the minimum,
  `argmin(b, k, n)`, with `k <= argmin(b, k, n) < n` and
  `b[argmin(b, k, n)] <= b[j]` for `k <= j < n`, the outer trace a trace of
  swaps of `k` with it (`perm_swaps` closes `perm` already);
- insertion sort: the inner loop is `insert(b, i)`, which keeps
  `sorted(b, 0, i)` and gives `sorted(b, 0, i + 1)`; its number of iterations
  is data-dependent, so its summary uses the iteration constraint
  `0 < j && x[j] < x[j - 1]` and the exit on the final array.

## Linear search

lsearch.dfy needs two lemmas: the iteration constraint `a[k] != x` over the
counter becomes `!occurs(x, selects(a, ⌊counter(0, 1, n)⌋))`, which a second
lemma instantiates at the index `k` of the postcondition, turning the
hypothesis `a[k] == x` of the split goal into `false`. Without `-split`, the
disjunction of the two exits remains, which needs a case split on `a[i] == x`.

## Generic fragment lemmas and induction lemmas (Oct 10, 2026)

The folder was renamed from `sorting` to `algorithms`. The two problems of
nested loops remain in the simplifier (the sharing of facts was reverted in
cb7aed7, which is why bubble_sort.dfy closes again with its summary lemma);
instead, [fragments.dfy](fragments.dfy) does by rewriting what the sharing did,
with lemmas on the fragments as `-teq` produces them, which close both minimal
problems and the nested-loop examples (candidates for teq.dfy):

- `invs_sums_counter`: the fragment `J == sums(X(k), maps(for ⌊K⌋ yield c))`
  with the sibling fragment `K == counter(0, 1, nn)` as a side condition
  (which binds the sequence `Ns` of the numbers of inner iterations) is
  `J == counter(X(k), c, nn)`; the initial value is higher-order, `X(k)`,
  since it is `0`, `k + 1` (selection sort), `i` (insertion sort), or the
  outer trace's value (nested_mult.dfy).
- `invs_current_counter`: `j == current(J)` with the counter fragment as a
  side condition is `j == X(k) + integer(nn) * c`.
- `invs_invs_counter_upper_zero`, `invs_exit_counter_zero`: the inner
  constraint `j < n` bounds the number of inner iterations, and the exit
  `n <= j` with it gives `j == n` in each outer iteration, which
  `sum_invs_const` of teq.dfy consumes (nested_sum.dfy).
- `invs_integer_consts`: `n == integer(nn)` in each iteration makes the
  sequence of inner lengths `⌊consts(m, natural(n))⌋`, which is substituted
  into the other fragments (nested_mult.dfy).
- `current_results_steps`: the outer trace of results whose relation to the
  previous value is known, `b == F(x, k)`, is the trace of the steps `F`.

Findings about the matching, each a workaround in a lemma and a candidate
for the tool:

1. **No backtracking over the selection of dependencies.** When the
   left-hand side binds `ks` to the first matching dependency (`⌊K⌋`) and a
   side condition then needs the fragment whose first dependency is another
   list (`⌊R⌋`, selected because the initial value `X(k)` matched its bound
   variable), the match fails; hence `invs_current_counter_other`, whose
   side condition has an independent first dependency `hs`.
2. **Side conditions must be in the normal form of the facts.** `X(k) +
   integer(nn)` does not match `integer(nn)` (a higher-order summand matches
   a single summand), and a conditional result `if X(k) <= n then ... else
   nn == zero` is decided by the simplifier in the fragment, so the condition
   of the next lemma does not see it; hence the `_zero` variants.
3. **Existing lemmas with a bound variable alone in a comparison are too
   eager.** The result `k + 1 + integer(nn) <= n` of the general constraint
   lemma is `k < n - integer(nn)`, which `above_iterations_def` of teq.dfy
   matches with the bound synthesized as a map, hiding the fact. Selection
   sort keeps the raw constraint as a side condition of its summary instead.
4. **Polymorphic lemmas with a higher-order variable in a side condition are
   not matched** (`current_results_steps<a>` with `F: (a, int) -> a` or
   `F: a -> a`), the monomorphic lemma is; `invs_current_counter_other<a>`
   with `X: a -> int` is matched, so the problem is the higher-order variable
   of the type parameter's type.
5. **Arithmetic in a quantified side condition is substituted before the step
   lemmas see it.** `i == k + 1` in the premise of the induction for insertion
   sort turns `sorted(F(b, k, i), 0, i + 1)` into `sorted(insert(b, k + 1), 0,
   k + 2)`, which the pattern `sorted(insert(b, i), 0, i + 1)` does not match;
   the premise is dropped (sound without it).
6. **Two definitions of a sequence are not combined.** If a fragment is turned
   into a second equation `⌊consts(m, n)⌋ == js` for a list `js` that already
   has a definition `js == maps(...)`, the goal `js == ⌊consts(m, n)⌋` stays
   (ice experiments, not in the files); the lemmas therefore produce the
   `invs` form `j == n` and not a definition of `js`.
7. **Equations are not propagated into bare arguments** (is_sorted.dfy, the
   remaining `integer(n') * n == m * n` of the nested loops): `mul_eq_cancel`
   is the workaround for the products; for is_sorted.dfy a lemma
   `sorted(a, lo, m + 1) <==> sorted(a, lo, n)` with `n == m + 1` as a side
   condition binds `n` to the first equation among the facts (`i == n₄ + 1`
   rather than `n == n₄ + 1`), so it stays open; further `-simplify` or
   `-split` passes do not help.
8. **Side conditions on `⌊results(...)⌋`** with a higher-order body are
   matched only monomorphically (4.); `v5b`-style binding of the dependency by
   a fresh variable plus an equation fails.
9. **Rule variables are not renamed apart from the variables of the goal.**
   If the goal has a free variable `Ns` and a lemma has a side condition with
   its own variable `Ns`, the open condition coincides with the fact literally,
   the simplifier decides it true without binding `Ns`, and `Rewrite.apply`
   reports "variables of a rule not instantiated by its match", an error that
   *replaces the goal* on stderr (a wrong assertion prints no goal either);
   hence the test methods of fragments.dfy name their sequences `KK, NN, JJ,
   jj`. Check stderr: a run with zero goals and an error is not a proof. The
   fragments of `-teq` are named `K?₁₄` etc. and never clash.

**Summaries of inner loops** (the approach of `current_results_bubble`)
work for selection sort (`current_selection_swaps`: the outer trace of swaps
of `k` with the result `m` of the inner loop becomes swaps with
`argmin(b, k, n)`) and for insertion sort with two pointers
(`current_results_insert`: the results become `insert(b, i)`); the original
insertion sort swaps `b[j]` and `b[j - 1]`, arithmetic on a bound variable of
the trace, which no pattern matches, so its inner loop cannot be summarized
(principle 8, two pointers). The summaries need the duplicate-variable trick
for closed side conditions (principle 9), `d == -1` for the step of the
counters down (literal `-1`), and the relation `i == k + 1` of two counters
as a closed `invs` side condition, which the simplifier decides.

**Induction lemmas replace the whole-loop lemmas.** `sorted_bubble_passes`,
which stated the correctness of bubble sort at once, is replaced by
`sorted_bubbled_steps`: a trace of steps `F` that keep an invariant indexed
by the iteration, `bubbled(b, k, len)` (the sorted suffix of length `k`,
partitioned from the prefix, clamped to the whole range), sorts, given the
quantified side condition `forall b, k :: 0 <= k < m && bubbled(b, k, len)
==> bubbled(F(b, k), k + 1, len)`, which the simplifier decides by the step
lemma `bubbled_pass` on one pass (as it decides that of `perm_steps`).
Selection sort uses `sorted_prefix_steps` with the invariant `sorted(b, 0, k)
&& partitioned(b, 0, k, n)` and two step lemmas on the swap with `argmin`;
insertion sort `sorted_prefix_steps_two` over two counters with `sorted(b,
0, i)` and `sorted_insert`. The induction lemmas must constrain all steps of
the trace: a side condition over `k < n` only, with `n <= m` steps, leaves
further steps unconstrained (unsound), hence `n == integer(m)` for selection
sort (a fact of the goal), no upper bound for insertion sort, and the clamped
predicate for bubble sort, whose number of passes is only known as a
disjunction (`n == zero || ... `) that is not split. With it, `passlen` is
not needed: the length `len - k - 1` of a pass may occur in the right-hand
side of the summary and in the side condition of the induction; only a
left-hand side may not contain it.

**Half-baked:** the abstract predicates `sorted`, `perm`, `partitioned`,
`bubbled`, and the functions `argmin`, `insert` are axiomatized by their
lemmas without definitions, so nothing checks the step lemmas (a Lean model
with definitions would); the summary lemmas depend on the exact shape and
order of the fragments, and their duplicated variables are noise that the
matcher should not need; `invs_current_counter_other` and the `_zero`
variants exist only because of findings 1 and 2; `mul_eq_cancel` papers over
the missing substitution; `perm_swaps_one`, `perm_steps_two`,
`sorted_prefix_steps_two` are arity variants of the same lemma (the
dependency lists would need a variadic pattern); the whole-loop lemma
`sorted_bubble_passes` is gone, but `current_selection_swaps` still fixes
`argmin` over `[k, n)` with `n` from the exit, i.e. it is specific to a loop
to `n`.

**Open:** is_sorted.dfy (finding 7), the `exists` postcondition of
max_element.dfy (no witness; a lemma whose left-hand side is the quantifier
is not matched, confirmed again), insertion_sort.dfy with one pointer
(arithmetic on a bound variable in the trace), and the two minimal problems
as problems of the simplifier (closed by lemmas only).

## Further algorithms (Oct 10, 2026, afternoon)

Eleven programs were written first, each with its specification, then
attempted in order; all programs are in the folder with their status in the
header. Verified (confirmed by exit status 0, see finding 18): prefix_sums,
distinct, three_way_partition, and later merge, counting_sort, insertion_sort
with one pointer (all `-teq -simplify`, wrong postconditions checked to leave
a goal). Open: row_sums and transpose (timeouts that were reported as
proved), cocktail_sort, first_duplicate, lower_bound, gnome_sort.

**What carried over.** The fragment lemmas of fragments.dfy resolve the inner
counters of every nested example without change; two more generic lemmas
were needed and should join them: `invs_subst_counter` (a fragment
`t == F(k, J)` about the inner counter `J` is stated about the counter;
higher-order `F` in the left-hand side is fine) and `earlier_invs_def` (the
element of a sequence at a position whose elements are given per iteration,
`earlier(natural(i), ts) == F(i)`, the instantiation of an invariant at a
witness). The summary-lemma approach (raw fragments as side conditions)
worked for distinct and cocktail sort, the count approach of partition.dfy
for the three-way partition, the recurrence lemma of teq.dfy for prefix sums
with a variant. transpose needed `current_results_steps` monomorphic for
arrays of arrays and a fold `column` of the inner loop.

**New findings** (continuing the numbering above):

10. **A higher-order variable for an array read is instantiated by the
    array.** `G(i)` against `a[i]` yields `G := a`, and the right-hand side
    then contains `a(i)` instead of `a[i]`, which no lemma matches
    (prefix_sums.dfy, hence the lemma reads the array directly).
11. **The simplifier does not decide `i == 0` from `0 <= i` and `!(1 <= i)`**
    in the else branch of a conditional whose then branch covers `1 <= i`;
    the lemma's conditional covers `0 <= j` instead (prefix_sums.dfy).
12. **Reproducibility.** cocktail_sort.dfy closed in one run (and a wrong
    postcondition left a goal), and leaves the whole goal in every later run
    of the same file and jar. Bisecting the 21 side conditions of its summary:
    the first three match, the fourth, the exit of the forward pass
    `invs(for ks, js check k, j :: n <= j + k + 1)`, does not, not even alone,
    with explicit dependencies, or renamed, although the fact has exactly
    that shape over `⌊K⌋, ⌊Lo⌋, ⌊Hi⌋, J?`; the same condition works in
    bubble_sort.dfy over `⌊K⌋, ⌊I⌋, J?`. Not explained; the one success
    suggests an order that depends on an unordered collection.
13. **A side condition is matched in the context of the fact's combinator,
    where other rules fire** (TODO.md on `sum_invs_const`, now
    `consts_prefix_def`). In first_duplicate.dfy this made a proof unsound:
    the condition `invs(for ⌊counter(0, 1, m)⌋, rs2 check k, r :: r == !nodup(a, k, n))`
    of `distincts_flags` was simplified by `nodup_distincts`, which rewrites
    `nodup(a, k, n)` to true under the hypothesis `distincts(...)` of the split
    goal, into `!r`, the constraint of the outer loop, a fact, so
    `distincts(...)` was proved from itself; without `nodup_distincts` the two
    goals remain, for the wrong postcondition too. Lesson: the side condition
    of a rule must not be simplifiable by rules that use the conclusion, and
    iteration constraints should be abstracted by atoms (`consts_prefix`
    style) that are matched literally.
14. **A literal disjunctive guard is never matched** (merge.dfy):
    `n <= j || i < m && a[i] <= b[j]` in a trace pattern, while a higher-order
    `G(i, j)` pinned by a quantified side condition `forall i, j :: G(i, j) <==> ...`
    is, which the simplifier decides by beta reduction. The mutual dependency
    of the pointers (`I` over `⌊J⌋`, `J` over `⌊I⌋`) is not the obstacle (a
    reduced program with the same loop matches), but tying the pointer lists
    to their traces is: as closed equations the conditions are decided and
    fail, as equations with an open trace variable they are not matched
    against the hypotheses (TODO.md). A variable argument of an
    uninterpreted function (`sorted(c, 0, n)`) is not expanded by its
    definition for subterm rewriting, so the whole atom must be the
    left-hand side, with the length as a variable `s` and `s == m + n` as a
    side condition (a pattern `m + n` of two variables is not matched).
15. **Atoms for fragments interfere with lemmas on fragments.** Abstracting
    each fragment of cocktail sort by an atom (`currents`, `passes_forward`,
    `counters`, `exits_forward`, ...) to make the summary's side conditions
    literal (the style of `consts_prefix`) fails twice: the definition lemma
    of the exit, whose left-hand side body is a bare comparison
    `n <= j + k + 1`, matches every comparison fact with `js` synthesized as a
    map (`2 k + 1 < n`, `0 <= integer(nn)`, inner constraints), and the atom
    for the inner counter consumes `K == counter(0, 1, nn)` before
    `invs_sums_counter` finds it as a side condition. Atoms work for
    structural fragments (`c == current(C)`, `C == bubble_pass(...)`), not
    for comparisons; the order of abstraction and use must be designed.

**Half-baked here:** `shake`, `shaken`, `nodup`, `merge`, `column`, `below`,
`beloweq` are abstract with their properties as lemmas (no definitions); the
summary lemmas repeat the whole fragment structure of each program; the
`_array` and monomorphic variants of lemmas exist only because of findings 4
and 10.

## The pin, the open trace variable, and atoms for hypotheses (Oct 10, 2026, evening)

Three workarounds, found on merge and counting sort, closed three more files
(insertion_sort with one pointer, merge, counting_sort; cocktail_sort stays
open, finding 12):

- **The pin.** A literal pattern that the matcher does not handle (a
  disjunctive guard, `j - 1` as a store index, `n - k - 2` as an initial
  value) becomes a higher-order variable `G(i, j)`, `Q(y, j)`, which matches
  anything, and a quantified side condition `forall i, j :: G(i, j) <==> φ`
  pins it to the intended term; the simplifier decides the pin by beta
  reduction. This makes the lemma sound and the pattern matchable, and it
  applies to every "not matched" item of TODO.md on patterns.
- **The open trace variable.** A side condition `Iv == trace(...)` with an
  open trace variable `Iv` is matched against the hypothesis `I == trace(...)`
  (the definition of the program's trace), and `is == ⌊Iv⌋` is then closed and
  trivial. This ties a dependency list to its trace, which a closed equation
  `is == ⌊trace(...)⌋` does not (it is decided by the simplifier, which does
  not expand `⌊I⌋`), and the same for `Iv == counter(0, 1, n)` against
  `I == counter(0, 1, n)`.
- **Atoms for quantified hypotheses.** A quantified precondition
  `forall i :: 0 <= i < n ==> 0 <= a[i] < k` is matched by no side condition,
  open or closed; the specification states it as an atom `keys_below(a, n, k)`,
  which a side condition with an open bound finds (counting_sort.dfy).

Further findings:

16. **A variable argument of an uninterpreted function is not expanded**
    when a pattern is matched below it: `selects(c, ...)` with `c == current(C)`
    is not matched by `selects(current(trace(...)), ...)` inside `count(...)`,
    but `selects(...)` as the left-hand side head is; the same for `sorted`.
    Hence the lemmas on merge rewrite `selects(current(...), ...)` to an
    abstract list first.
17. **The simplifier splits a conjunctive constraint into fragments**, so a
    pinned test `D(y, j) <==> (0 < j && y[j] < y[j - 1])` is false for the
    fragment `y[j] < y[j - 1]` alone; the pin must follow the fragments.

## Summary of the state (Oct 10, 2026, end of the day)

**Verified, confirmed by a terminating run** (`-teq -simplify`, exit status 0,
wrong postconditions leave a goal): lsearch, perm, bubble_sort,
selection_sort, insertion_sort (one pointer), insertion_sort2 (two pointers),
nested_counter, nested_sum, nested_mult, fragments, inner_loop_flat,
count_occurrences, max_element (with `occurs`), argmax, partition, reverse,
prefix_sums, distinct, three_way_partition, merge, counting_sort. The
whole folder runs in about five minutes on one core, 5 to 35 s per file.

**Open:** row_sums, transpose (the substitution lemmas cycle), cocktail_sort
(the exit condition of the forward pass is not matched), first_duplicate
(early exit; two goals remain after the circular rule was removed),
lower_bound (the summary cycles through its exit condition), gnome_sort (no
counter), is_sorted (equation propagation), the `exists` of max_element, and
the two minimal problems as problems of the simplifier.

**What works as a method:**

1. Generic fragment lemmas (fragments.dfy) resolve the inner counters of
   every nested loop: `invs_sums_counter`, `invs_current_counter`,
   `invs_invs_counter_upper_zero`, `invs_exit_counter_zero`,
   `invs_integer_consts`, `invs_current_counter_other`. They terminate in all
   files, although their side conditions are `invs`, since their left-hand
   sides are specific fragments.
2. Summary lemmas take the fragments of an inner loop as side conditions and
   rewrite the outer trace into a trace of an abstract step (`shake`,
   `insert`, swaps with `argmin`, `nodup`), with the duplicate-variable trick
   for closed conditions; `current_results_steps` for inner results that are
   a function of the previous value.
3. Induction lemmas with the invariant indexed by the iteration
   (`bubbled`, `shaken`, `sorted_prefix_steps`) and a quantified side
   condition that the simplifier discharges by step lemmas on atoms; all
   steps of the trace must be constrained.
4. The pin for literal patterns the matcher does not handle, the open trace
   variable to tie a dependency to its trace, and atoms for quantified
   hypotheses (previous section).
5. Rules on the atoms of the postcondition for named results (`argmin`,
   `lb`, `below`, `beloweq`, `rank_table`, `merged`).

**Findings about the tool**, numbered 1 to 17 above and:

18. **A run that is killed by the timeout prints no goal, and a runner that
    counts goals reports it as proved.** row_sums.dfy and transpose.dfy, the
    first "closed" runs of lower_bound, and the "inconsistent hypotheses" of
    its exit condition were all timeouts (120 s). Every status in this folder
    was re-established with the exit status checked (`exit status: 0`) on
    Oct 10 in the evening; the two files that time out are marked open.
    Check `./Cuvee.sh -test`-style expectations with the status, never the
    count of goals alone.
19. **General left-hand sides with `invs` side conditions cycle**, as
    TODO.md says for `sum_invs_const`: `invs_subst_counter` (body
    `t == F(k, J)`), `invs_subst_sums`, `invs_subst_column`, and
    `earlier_invs_def` (left-hand side `earlier(natural(i), ts)`, which the
    reads of every combinator context match) do not terminate on row_sums and
    transpose. The remedy to try: definitions of the sequences as maps
    (`Js == maps(for ks yield k :: counter(0, 1, nn))`), which the simplifier
    substitutes, with a structural lemma for
    `earlier(natural(i), maps(for ⌊counter(0, 1, m)⌋ yield k :: F(k)))`.
20. **A side condition on the current value of the trace being rewritten is
    re-entrant** (lower_bound.dfy): deciding `current(Hv) <= current(Lv)`
    rewrites `current(Lv)` by the lemma itself, whose conditions decide it
    again; the exit of a loop must be taken from the facts (`hi <= lo` of the
    goal, bound by open variables and identified with the current values)
    or abstracted by an atom.
21. **The name of a method variable must differ from the lemma's variables
    in pins**: a pin `forall lo, hi :: G(lo, hi) <==> a[(hi + lo) / 2] < x` can
    only be decided if `x` is bound; in lower_bound.dfy it was bound by name
    capture only (finding 9). A pin must mention variables that the
    left-hand side or an earlier condition binds.

**Candidates for teq.dfy:** the fragment lemmas of fragments.dfy,
`results`, `current_results_steps`, `current_trace_all`, `mul_eq_cancel`,
`sum_selects_cons`, `sum_selects_zero`, `current_trace_prefix_sums_array`,
`current_trace_histogram`, `perm_steps`, `perm_swaps_one`; the induction
lemmas and the abstract predicates of sorting as a sorting library.

## Candidates for teq.dfy and the cycling of `invs` side conditions (Oct 11, 2026)

The mechanism, from TODO.md (the entry on `sum_invs_const`) and
doc/simplifier.md: an open `invs` side condition is matched against the
`invs` facts; matching it against a fact builds the simplifier's context of
that fact's combinator, in which the reads of the dependencies
`earlier(natural(k), ⌊X⌋)` are rewritten by all rules. If the left-hand side
of the rule being decided matches one of those rewritten reads (`sum(js)`
matched the `sum(prefix(...))` that `earlier_sums` produces), the rule is
tried again inside, with the same fact, one level deeper, until the budget
is exhausted. Two ingredients: an `invs` side condition over lists that the
left-hand side binds, and a left-hand side general enough to match inside
that context. TODO.md's static criterion ("no `invs` in a side condition
whose dependencies are variables of the left-hand side") flags the first
ingredient alone; the lemmas below show that the second decides.

The candidates from this folder (first group of the answer of Oct 11),
against the mechanism:

| lemma | `invs` condition over lists of the lhs | lhs general? | verdict |
| --- | --- | --- | --- |
| `invs_sums_counter` | yes (`ks, Ks`, binds `Ns`) | no: an `invs` with the body `J == sums(X(k), map(...))` | safe; terminates in all files |
| `invs_current_counter`, `_other` | yes | no: body `j == current(J)` | safe |
| `invs_invs_counter_upper_zero` | yes | no: a nested `invs` with `x < n` | safe |
| `invs_exit_counter_zero` | yes (`ks, js`) | **yes**: body `n <= j` with open `n` matches every comparison fragment, `js` synthesized as a map (finding 15) | risky: tried on every comparison fragment of every program; restate with the exit as an atom or a specific body |
| `invs_integer_consts` | none | body `n == integer(nn)` with open `n` matches any equation fragment with `integer` of a bound variable | no cycle, but spurious matches; give it the shape of `consts_prefix_def` (an `earlier` read) |
| `current_results_steps` | yes, exactly the lists of the lhs (the TODO criterion verbatim) | no today: `current(results(...))` arises from a read only if some rule rewrites `earlier(k, ⌊results(...)⌋)` into a `current` | safe now (nested_mult, 10 s); latent: an `earlier_results` lemma, the natural counterpart of `earlier_sums`, would create the cycle |
| `current_trace_all`, `current_trace_histogram`, `current_trace_prefix_sums_array`, `sum_selects_cons`, `sum_selects_zero`, `earlier_maps_counter`, `mul_eq_cancel` | none (arithmetic conditions are decided, not searched) | various | no cycle of this kind; `mul_eq_cancel` is tried on every equation with a common factor, a cost |
| `invs_subst_counter`, `invs_subst_sums`, `invs_subst_column` (not candidates) | yes | **yes**: higher-order bodies `t == F(k, J)` match almost any equation fragment | cycle confirmed: the timeouts of row_sums and transpose (finding 19) |
| `earlier_invs_def` (not a candidate) | yes (`ts` of the lhs) | **yes**: `earlier(natural(i), ts)` matches the reads that the context of its own condition rewrites | cycle confirmed |

Rule of thumb for new lemmas with `invs` side conditions: the left-hand
side must be a term that no rewriting of a read `earlier(natural(k), ⌊X⌋)`
can produce, i.e. an `invs` fragment with a specific body, or an atom of the
specification; never a bare read, comparison, equation, or `current` of a
named trace for which an `earlier_...` acceleration lemma exists or may be
added. Abstracting the constraint by an atom first (`consts_prefix_def`
style) and taking the atom as the side condition is always safe.

Empirical check (`-include` of the candidates into the existing tests, one
core, 120 s per file): see the next entry.

**Empirical check of the candidates (Oct 11):** the candidates (the first
group above, as `resources/cuvee/teq/nested.dfy` plus `current_trace_histogram`,
`current_trace_prefix_sums_array`, `sum_selects_cons`, `sum_selects_zero`,
`earlier_maps_counter`, `mul_eq_cancel`) injected by `-include` into the
twelve examples of `examples/dafny/teq` and every fourth recorded task of
`benchmarks/sv-comp/dafny/expected.csv` (68 tasks), one core, 120 s per
file: no task changed its number of goals, none timed out, the mean time was
11 s and the maximum 66 s (`ss1`, an expected error). The two apparent
mismatches, `linear-inequality-inv-c` (unresolved `below_prefix`) and
`array_init_var_plus_ind` (one goal), occur without the candidates too: the
jar of the check predates the lemmas `below_prefix` and `triangle_nonneg` of
the current teq.dfy. The examples without `-teq` (bsearch, copy, counter,
init, rules, swap) cannot take the injection, since it needs `Trace`.
So the candidates are compatible with the existing tests as far as sampled;
the cost of `invs_exit_counter_zero` on comparison fragments (above) did not
show in the times.

## The modules of the database and the tests (Oct 11, 2026, afternoon)

teq.dfy was split into the modules of `resources/cuvee/teq`, which `-teq`
injects in order (`core`, `arithmetic`, `counters`, `aggregation`, `arrays`,
`search`), and two further modules that a file includes on demand with
`-include teq:<concept>`: `nested` (the fragment lemmas of fragments.dfy,
`results`, `current_results_steps`, `current_trace_all`, `current_trace_last`,
`consts_prefix_integer`) and `sorting` (`sorted`, `perm`, `partitioned`, the
lemmas on swaps and steps, the prefix inductions). This folder is a test
suite now: each file's first line is its command line and `name.out` its
expected output (`name.err` only if there is one); row_sums and transpose
are listed in `Examples.nonterminating` and not run. Regenerate an output by
hand with `./Cuvee.sh <options> <file> > name.out 2> name.err`, remove an
empty `.err`, and check the exit status, not the count of goals (finding 18).

What injecting the `nested` module taught, by attempting it for all files at
once first:

22. **A summary lemma is tied to the forms of the fragments it sees.** With
    the fragment lemmas injected before the file's lemmas, the fragments of
    an inner loop are resolved (`J == counter(0, 1, nn)`, `j == integer(nn)`,
    `integer(nn) + j == k + 1`) before a summary that expects the raw forms
    (`J == sums(...)`, `j == current(J)`) can match. bubble_sort.dfy was
    adapted to the resolved forms and includes `teq:nested`; insertion_sort
    and insertion_sort2 keep their file-local lemmas and do not include it,
    since their adapted summaries did not fire (the 17th condition, the
    equations identifying the exit's lists, failed, not isolated).
    Rule: a lemma that takes fragments as side conditions must be written
    for the normal form that the whole database, including the modules
    included, gives the fragments, and a file should include only the modules
    its lemmas are written for.
23. **The order of modules decides which abstraction a fragment gets.** With
    `aggregation` before `nested`, the exit `j == n` of an inner counter is
    abstracted by `consts_prefix_def` into `consts_prefix(m, n, J?)` before a
    lemma of `nested` could derive `n == integer(nn)` from it; hence
    `consts_prefix_integer`, with the atom as the left-hand side (which binds
    `n`) and the fragment of the final values as the side condition (which
    binds `Ns`): `consts_prefix(m, n, js) <==> Ns == ⌊consts(m, natural(n))⌋`.
    A version with the atom as an *open side condition* raised "variables of a
    rule not instantiated" (`n` unbound), although open atoms are said to be
    searched among the facts; a version with the body `n == integer(nn)` as
    the left-hand side matched unrelated equation fragments (finding 15).
24. **The `nested` module makes rewriting cycle on cocktail sort** ("rewriting
    does not terminate"), on the program alone without any file lemma; the
    first half of the module (`invs_sums_counter` to
    `invs_exit_counter_zero`) suffices to cause it, the single lemma is not
    isolated. The suspect is `invs_exit_counter_zero` (finding 15 and the
    termination table above), whose bare comparison body matches every
    comparison fragment of a program with three counters. cocktail_sort does
    not include the module.
25. **Duplicate declarations are accepted** when a file declares a lemma or
    function identically to an injected module (the files of this folder
    keep their local copies), but the method's variables must be named apart
    from the lemmas' variables (finding 9), which invs_counter_equation.dfy
    needed once `teq:nested` was included.
26. **The harness runs the roundtrip of an output with the options of its
    command line**, so `-include teq:<concept>` must be passed through
    (`Examples.options`), or an output that mentions a module's function
    (`results`) does not parse back.

Lean: the database is printed by
`./Cuvee.sh -known dfy -print lean -include teq:core -include teq:arithmetic ... empty.dfy`;
without `-teq` the included modules are not hidden. The output equals the
one from teq.dfy modulo order; `half_even` was dropped from teq.dfy between
the split and the commit, so the modules are a snapshot: regenerate them from
teq.dfy by the split (by declaration name, with the preceding comments) if
teq.dfy changes before it is retired.

State of the files with respect to the modules: bubble_sort, nested_mult,
invs_counter_equation, invs_fragments use `teq:nested` (the last two are
verified only by it); all others use the six base modules and their own
lemmas, with the results of the morning; the sorting lemmas of the examples
are duplicated in `teq:sorting`, which no file includes yet.

## The pending threads resolved (Oct 11, 2026, evening)

The open threads were worked on in a folder `pending/` (not committed) with
diagnostics that are worth keeping as techniques: *pair runs* of single lemmas
of a module to find a cycling pair, *truncated copies* of a summary lemma with
its first k side conditions to find the first failing one, and *probes*: rules
with the real left-hand side, the first k side conditions and a fresh atom
`probe_k(...)` as right-hand side, k downwards, so that the goal shows the
largest k whose conditions hold. Every result was checked on a program with a
wrong postcondition, which must leave a goal. Four files are verified now
(cocktail_sort, first_duplicate, row_sums, transpose), the `nested` module is
restated, lower_bound remains open for reasons of the engine.

27. **A closed `invs` condition over variables bound by earlier conditions
    is decided, not matched, and fails** (cocktail_sort.dfy). The summary
    `current_results_shake` fired with its first 20 side conditions and not
    with the 21st, `invs(for ks, js4, Js3 check k, j, J :: j == current(J))`,
    whose variables were all bound: the same condition for the forward pass
    (condition 7) uses fresh `js5`, `Js5` and succeeds. The fix is the pattern
    of bubble_sort: fresh variables and identifying equations. Neither the
    extra dependencies of the fact (the traces of `lo` and `hi`; a diagnostic
    with two and four dependencies matched both) nor the name of the rule
    variable `n` (finding 21; renamed to `len` without effect) was the cause.
    The run of Oct 10 that closed the goal once (finding 12) presumably
    decided the closed condition by chance.
28. **A bound that is not a difference constraint is not decided from two
    facts** (cocktail_sort.dfy): `len <= 2 * integer(m) + 1` is not derived
    from `n <= integer(m) + lo + 1` and `lo == integer(m)` (finding 11 again).
    The induction lemma states the bound in the goal's form, `l == integer(m)`
    with `l` open, matched against the equation of `lo`, and
    `len <= integer(m) + l + 1`, which is the fact.
29. **A bare bound variable on one side of a fragment's body is synthesized
    as a map.** The pair runs of the five lemmas of the first half of the
    `nested` module on the cocktail program showed that the exit lemma
    `invs_exit_counter_zero` cycles with each of the four others and alone
    with none: its left-hand side `invs(for ks, js check k, j :: n <= j)`
    matches every comparison fragment with `js` synthesized as a map (finding
    15), and its `invs` side conditions build the combinator contexts in which
    the counter lemmas and then the exit lemma fire again. A restatement with
    the left-hand side `invs(for ks, Ns, js check k, nn, j :: j == integer(nn))`
    removed the cycle on cocktail sort and introduced one on nested_mult:
    `j` alone on one side is synthesized just as well, and matches
    `r' == r + integer(nn)`. The left-hand side that works is the constraint
    fragment `invs(for ks, Ns check k, nn :: integer(nn) <= n)`, a function
    symbol on the side of the bound variable, with the exit and the final
    values as side conditions over fresh variables; it produces `j == n` (which
    `consts_prefix_def` abstracts) and `nn == natural(n)`, which the new
    `invs_natural_consts` turns into `Ns == ⌊consts(m, natural(n))⌋`. The
    module is now this; a compatibility run over all algorithms agrees with the
    expected goals except where summaries are written for the fragment forms
    without the module (insertion_sort, insertion_sort2, finding 22) and for
    invs_fragments, whose method variables were named like the rule's
    (finding 21; renamed).
30. **The chain for an inner result stored at the outer position**
    (row_sums.dfy, transpose.dfy): with the module, the goal has the exit
    abstracted (`consts_prefix(m, n, J?)`), `N? == ⌊consts(m, natural(n))⌋`,
    and the inner counters, sums (or stores) and final values as fragments
    over separate lists. The substitution lemmas with general left-hand sides
    (finding 19) are replaced by one specific lemma per step: the counters
    over the constant numbers of iterations (the dependency
    `⌊consts(m, natural(n))⌋` as a pattern is matched through the context),
    the inner sums (stores) over the inner counter, the final values of inner
    traces given per iteration (higher-order `T == G(k)` as a side condition
    over a fresh list), sums given per iteration as a `maps`, and the element
    of a `maps` over the counter at the position of the postcondition. Each
    step takes the fragment it depends on as a side condition over a fresh
    list variable, identified by an equation. Both files verify in under two
    minutes on one core.
31. **The exit of an outer loop in the conclusion is a disjunction that no
    rule sees** (first_duplicate.dfy). The summary of the inner loop fires,
    the simplifier turns the pointwise fragment of the results into a `maps`,
    so the final flag is `r == current(results(false, ⌊K⌋, maps(for ⌊K⌋ yield k :: !nodup(a, k, n))))`,
    and the outer counter and the flag trace are the variables `K`, `R` with
    their equations as hypotheses: lemmas with `⌊counter(0, 1, m)⌋` as an
    argument never match (the open trace variables `Kv == counter(0, 1, m)`,
    `Rv == results(false, ⌊Kv⌋, rs)` do, matched against the hypotheses). The
    flags at the heads, `invs(for ⌊K⌋, ⌊R⌋, ⌊I⌋ check k, r, i :: !r)`, carry
    the unused dependency `⌊I⌋`, which the simplifier drops from a closed
    instance, so the condition is written over an open list `hs` and
    `hs == ⌊Rv⌋` afterwards. The probes then showed the last condition failing:
    the exit `n <= i || r`, a closed disjunction, is not decided, since the
    goal's conclusion is `i < n && !r || r == !distincts(...)`, which `-split`
    does not split, and the context of the second disjunct does not contain
    the literals of the negated first. With the postcondition as the two
    implications `r ==> !distincts(...)` and `!r ==> distincts(...)`, each
    goal has its literal (`r`, respectively `n <= i`) in the context of the
    atom, and one rule per case closes it. Also seen: an instantiated
    higher-order variable leaves a beta-redex `((k: int) => !nodup(a, k, n))(k)`
    in the output.
32. **A rule is applied while the instances of its own side conditions are
    simplified** (lower_bound.dfy). The summary `current_lower_bound` fires
    and the four properties of `lb(a, n, x)` close the postconditions when the
    exit is a comparison `h <= l` of two open variables, matched against the
    fact `hi <= lo`; but then `h` and `l` are not tied to the traces and the
    rule is not sound as a lemma. Every sound tie fails: `l == current(Lv)`
    with `Lv` bound, closed or open, is simplified before it is decided or
    matched (`Rewrite.conditions`), which rewrites `current(Lv)` by the lemma
    itself (re-entrant, finding 20; the same reason bubble_sort's summary takes
    `current(results(...))` as left-hand side instead of `results(...)`).
    With `Lv` open, `l == current(Lv)` binds `Lv` and `l` from the hypothesis,
    but the probes showed that **a left-hand side matched against `current(Lo)`
    through the definition of the trace variable `Lo` leaves its dependency
    variables `nn`, `hs` unbound** (a probe fired with "variables of a rule not
    instantiated"), and the trace condition that would bind them no longer
    matches once `Lv` is bound (its instance is simplified with `Lo` replaced).
    A guard in the engine (the rule disabled while its conditions are
    evaluated) would make the sound version work.
33. **The checkout's jar must not be used for long runs**: a rebuild during a
    run crashes the running JVM with `NoClassDefFoundError`, and a build from
    a working tree with changes is not the committed state; run from a private
    copy of the jar. The results above were produced with a copy of the jar of
    c8a3cec7; the expected outputs of the four verified files and of
    invs_fragments must be regenerated after the assembly of this commit.

## Proposals (Oct 11, 2026, end of the day)

Ordered by expected payoff; the engine items are the ones that would remove
the workarounds now in every summary lemma.

Engine (TODO.md has the observations):

1. **A re-entrance guard**: a rule is not applied, or the instance is not
   rewritten, while its own side conditions are evaluated. This makes the
   sound summary of lower_bound.dfy work (the ties `l == current(Lv)`),
   removes the `current(results(...))` workaround from the summaries, and
   admits conditions on the rule's own term in general. Smallest change,
   largest effect.
2. **Closed `invs` conditions matched modulo unused dependencies** instead of
   decided: the fresh-variable-plus-equation pattern (five files now) becomes
   unnecessary and the summaries shrink by a third.
3. **A left-hand side matched through a trace variable's definition binds all
   its variables**, or the match is refused there, instead of firing later
   with "variables of a rule not instantiated by its match" (finding 32).
4. **`Rule.check` rejects a left-hand side with a bare bound variable of a
   variable dependency together with an `invs` side condition** (finding 29);
   it would have refused the exit lemma of the nested module on load.
5. **`-split` splits the negated exit** when the conclusion is `¬exit ∨ post`
   with a disjunctive exit, one goal per literal (finding 31); then the
   postcondition of first_duplicate.dfy can be the equivalence again.

Database:

6. The chain lemmas of row_sums.dfy and transpose.dfy (finding 30) into the
   `nested` module in generalized form: counters over constant numbers of
   iterations, final values of traces given per iteration, pointwise
   definitions as `maps`, reads of a `maps` over the counter. Most nested
   loops with a stored inner result need exactly this chain.
7. The summaries of insertion_sort.dfy, insertion_sort2.dfy and
   cocktail_sort.dfy restated for the fragment forms of the module
   (finding 22), so that `nested` can become part of `-teq`; the
   compatibility run shows these three files as the only obstacle.
8. Lean proofs for the `nested` module, which has none; the restated exit
   lemma and `invs_natural_consts` are small.

Algorithms:

9. gnome_sort.dfy needs an idea rather than a lemma: the number of iterations
   is not a counter and the position moves in both directions, so an
   abstraction by a potential (the invariant "sorted up to the position" with
   the position's trace characterized by its bounds), in the style of the
   lower bound.
10. is_sorted.dfy is one substitution of the exit into `sorted` away
    (finding 7 of the principles), presumably a two-line lemma on the exit;
    max_element.dfy with `exists` waits for quantified left-hand sides or a
    witness trace (principle 4).

Infrastructure:

11. The probe technique as a flag, `-probe <lemma>`, which reports the first
    side condition of a named rule that fails on a goal, with the facts it
    was matched against: the truncated copies and probe files of today took
    an afternoon for information the engine has.
12. A `-timeout` that reports the killed goal instead of printing nothing: a
    silent kill looked like a proof twice this week (finding 18).

## The proposals worked on (Oct 11, 2026, night)

Of the proposals above, those without Scala changes: 6 (the chain into the
module), 7 (the summaries for the module's forms), 9 (gnome sort), 10
(is_sorted). Runs on one core from a private copy of the jar of 1a20a02c.

34. **A lemma of the module `nested` does not fire where the identical lemma
    in the input does.** The three chain lemmas of row_sums.dfy were moved into
    the module, after `consts_prefix_integer`; row_sums then leaves one goal,
    with the fragments of the inner counters and `N? == ⌊consts(m, natural(n))⌋`
    untouched, and `-rules` lists `invs_counter_consts` neither among the
    used rules; the same lemmas included once more as a user file close the
    goal, and `-rules` listed them before (`invs_counter_consts` twice,
    `invs_sums_selects_counter` eight times). The texts are identical, and the
    module's `invs_counter_consts` does fire on transpose.dfy, whose program
    has the same variables `m`, `n`, `A`. Variants of the module (the rule
    variables `m`, `n` renamed, the chain at the end) could not be run, since
    including them as user files gave a parse error at the first line of the
    input, which is not understood either. The module keeps
    `invs_counter_consts` (transpose needs it there), row_sums.dfy keeps
    `invs_sums_selects_counter` and `invs_maps_sum` locally. A candidate for
    TODO.md: whether rules from an injected module and from the input are
    treated alike (the attributes differ by `{:teq}`), and whether the order
    of rules matters for a fragment that several rules could rewrite.
35. **Two rules for the exit of is_sorted.dfy did not help.** The goal is
    `s == sorted(a, 0, n' + 1) && n == n' + 1 ==> s == sorted(a, 0, n)`. A
    rule `sorted(a, 0, m + 1) <==> sorted(a, 0, n)` with `n == m + 1` as side
    condition matched the equation `i == n' + 1` of the final value of `i`
    first, both equations match, and rewrote the hypothesis to
    `sorted(a, 0, i)`. A rule `sorted(a, 0, x) <==> sorted(a, 0, m + 1)` with
    `x == m + 1`, or `m == x - 1`, did not fire at all, presumably since the
    instance of the condition is simplified with the solution of the exit
    before it is matched, and the orientation in which the equation is
    stored is not visible in the goal. A rule that rewrites both bounds to
    one form also risks a cycle between the two forms. The file is reverted
    and stays open; a sound fix is finding 32's engine guard or the
    substitution of solutions into function arguments (TODO.md).
36. **Gnome sort is verified** (gnome_sort.dfy), contrary to its status "open
    as expected". The position and the array are traces over each other with
    the guard `i == 0 || b[i - 1] <= b[i]`, swaps at `i` and `i - 1`, and a
    number of iterations unrelated to `n`. The lemma `sorted_gnome` is on the
    whole atom `sorted(current(trace(a, for ⌊Kv⌋, ⌊Iv⌋ do b, k, i :: case G(i, b) => b case !G(i, b) => b[Q(i) := b[P(i)]][P(i) := b[Q(i)]])), 0, n)`
    (merge.dfy), with the guard `G` and the positions `P`, `Q` higher-order
    and pinned, the trace of the array tied first (`Bv == trace(a, for ⌊Kv⌋, ⌊Iv2⌋ ...)`,
    open in `Bv`, `Iv2`, then `Iv2 == Iv`), the trace of the position tied
    second (`Iv2 == trace(1, for ⌊Kv2⌋, ⌊Bv2⌋ do i, k, b :: case G(i, b) => i + u case !G(i, b) => i + d)`
    with fresh `Kv2`, `Bv2`, `u`, `d`, identified afterwards, since literals
    and arithmetic on bound variables are not matched), the exit through
    `x == current(Iv)` and `n <= x`. The invariant is `sorted(b, 0, i)`: a
    step up extends the sorted prefix, a swap down keeps the prefix below
    sorted, and at the exit the prefix covers the range; `perm_gnome` states
    that every step is the identity or a swap. The wrong postcondition
    `sorted(b, 0, n + 1)` leaves a goal. The lesson: a data-dependent number
    of iterations is no obstacle when the invariant can be stated on the
    final values alone and the lemma is written on the atom of the
    postcondition.
37. **The module `nested` can become part of `-teq`** as far as the
    algorithms are concerned: with insertion_sort, insertion_sort2 and
    cocktail_sort restated for the module's fragment forms (the final values
    of the inner counters as `integer(nn) + j == k + 1`, `j == integer(nn) + k`,
    `integer(nn) + j + k + 2 == len`, written as the goal prints them), all 30
    files agree with their expected goals when the module is included
    (round 7 of the runs), and nothing cycles. The remaining step is the
    Scala change in `TEQ.modules`, and a run on the SV-COMP translations.
