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
| [insertion_sort.dfy](insertion_sort.dfy) | `perm` verified, `sorted` open: swaps at `j - 1`, arithmetic on a bound variable |
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
