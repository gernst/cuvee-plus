# Algorithms with trace equation systems

Experiments towards sorting and other array algorithms with nested loops with
`-teq -simplify`, in the dialect of Dafny of Cuvée: arrays are total maps `array<int, int>`, the first `n`
elements are sorted. Each file states its command line in its first line and
its status in its header; the lemma database `teq.dfy` is injected by `-teq`,
the lemmas specific to the examples stand at the beginning of each file.

| file | status |
| ---- | ------ |
| [lsearch.dfy](lsearch.dfy) | verified (`-teq -split -simplify`) |
| [perm.dfy](perm.dfy) | verified: permutations by swaps in single loops |
| [bubble_sort.dfy](bubble_sort.dfy) | verified: nested loops, `sorted` by the induction lemma, `perm` |
| [selection_sort.dfy](selection_sort.dfy) | verified: summary of the inner loop, `sorted` by the induction lemma, `perm` |
| [insertion_sort.dfy](insertion_sort.dfy) | verified: the swaps at `j - 1` as pinned higher-order positions |
| [insertion_sort2.dfy](insertion_sort2.dfy) | verified: the same with two pointers, summary and induction lemma |
| [nested_counter.dfy](nested_counter.dfy) | verified: the simplest nested loop |
| [nested_sum.dfy](nested_sum.dfy), [nested_mult.dfy](nested_mult.dfy) | verified: the generic fragment lemmas |
| [fragments.dfy](fragments.dfy) | verified: the generic fragment lemmas on the two minimal problems |
| [inner_loop_flat.dfy](inner_loop_flat.dfy) | verified: the facts of an inner loop at the top level |
| [invs_counter_equation.dfy](invs_counter_equation.dfy) | open: problem 1, minimal (closed with the lemmas of fragments.dfy) |
| [invs_fragments.dfy](invs_fragments.dfy) | open: problem 2, minimal (closed with the lemmas of fragments.dfy) |
| [count_occurrences.dfy](count_occurrences.dfy) | verified: the count named as the normal form |
| [max_element.dfy](max_element.dfy) | verified with `occurs`; open with `exists` (no witness) |
| [argmax.dfy](argmax.dfy) | verified: a selection trace with rules on the atoms |
| [partition.dfy](partition.dfy) | verified: Lomuto partition, conditional swaps at a count |
| [reverse.dfy](reverse.dfy) | verified: two pointers, `-simplify -split -simplify` |
| [is_sorted.dfy](is_sorted.dfy) | open by one substitution of the exit into `sorted` |
| [row_sums.dfy](row_sums.dfy) | open: the substitution lemmas cycle (timeout reported as proved, finding 18) |
| [transpose.dfy](transpose.dfy) | open: as row_sums, the substitution lemmas cycle |
| [prefix_sums.dfy](prefix_sums.dfy) | verified: the recurrence with the term at the written position |
| [distinct.dfy](distinct.dfy) | verified: nested loops with a flag, summary and `current_trace_all` |
| [three_way_partition.dfy](three_way_partition.dfy) | verified: Dutch flag by a single scan, two counts |
| [cocktail_sort.dfy](cocktail_sort.dfy) | open: closed once, the exit condition is not matched since (finding 12) |
| [first_duplicate.dfy](first_duplicate.dfy) | open: early exit; a circular side condition made an attempt unsound |
| [merge.dfy](merge.dfy) | verified: pinned higher-order guard, pointers tied by open trace variables |
| [counting_sort.dfy](counting_sort.dfy) | verified: four loops in sequence, the key range as an atom |
| [lower_bound.dfy](lower_bound.dfy) | open: the summary with the exit as a side condition cycles |
| [gnome_sort.dfy](gnome_sort.dfy) | open, as expected: the number of iterations is not a counter |

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
