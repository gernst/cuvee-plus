// sorting: the abstract predicates sorted and perm (permutation as a total map on the indices, so that a swap at any
// two positions preserves it) and partitioned, with the generic lemmas on traces of swaps and of steps, and the
// inductions for sorting by a growing sorted prefix, with the invariant as a quantified side condition that the
// simplifier decides by step lemmas on atoms; the algorithms' own knowledge (the summaries of their inner loops, the
// step lemmas, argmin, insert, bubble_pass) stays with the examples in examples/dafny/algorithms, Oct 11, 2026; this
// file assumes the core declarations of teq.dfy (Nat, integer, List, Trace, current, butlast, counter) and
// counters.dfy; the predicates are declared without definitions, their meaning is the lemmas (a definition in Lean
// would make the lemmas provable)

// a[lo..hi) is nondecreasing
function {:teq} sorted(a: array<int, int>, lo: int, hi: int): bool

// a is a permutation of b as a total map on the indices
function {:teq} perm(a: array<int, int>, b: array<int, int>): bool

// all of a[lo..mid) are at most all of a[mid..hi)
function {:teq} partitioned(a: array<int, int>, lo: int, mid: int, hi: int): bool

// the empty range and ranges of one element are sorted, the empty prefix is partitioned from the rest
lemma {:rw} {:teq} sorted_empty(a: array<int, int>, lo: int)
  ensures sorted(a, lo, lo) <==> true

lemma {:rw} {:teq} sorted_short(a: array<int, int>, lo: int, hi: int)
  requires hi <= lo + 1
  ensures sorted(a, lo, hi) <==> true

lemma {:rw} {:teq} partitioned_empty(a: array<int, int>, lo: int, hi: int)
  ensures partitioned(a, lo, lo, hi) <==> true

lemma {:rw} {:teq} partitioned_whole(a: array<int, int>, lo: int, hi: int)
  ensures partitioned(a, lo, hi, hi) <==> true

// no descent between the adjacent positions k and k + 1 for k below n means sorted up to n + 1
// (from is_sorted)
lemma {:rw} {:teq} sorted_def(a: array<int, int>, n: Nat)
  ensures invs(for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ check k, i :: a[k] <= a[i]) <==> sorted(a, 0, integer(n) + 1)

// permutations

lemma {:rw} {:teq} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

// a swap preserves the permutation
lemma {:rw} {:teq} perm_swap(a: array<int, int>, b: array<int, int>, p: int, q: int)
  ensures perm(a[p := a[q]][q := a[p]], b) <==> perm(a, b)

// a trace of swaps at positions that depend on the state and the iteration preserves the permutation, a higher-order
// pattern; for one and for two dependencies
// (from perm, selection_sort)
lemma {:rw} {:teq} perm_swaps_one(a: array<int, int>, b: array<int, int>, ks: List<int>,
                                  P: (array<int, int>, int) -> int, Q: (array<int, int>, int) -> int)
  ensures perm(current(trace(a, for ks do x, k :: x[P(x, k) := x[Q(x, k)]][Q(x, k) := x[P(x, k)]])), b)
    <==> perm(a, b)

lemma {:rw} {:teq} perm_swaps(a: array<int, int>, b: array<int, int>, ks: List<int>, hs: List<int>,
                              P: (array<int, int>, int, int) -> int, Q: (array<int, int>, int, int) -> int)
  ensures perm(current(trace(a, for ks, hs do x, k, h :: x[P(x, k, h) := x[Q(x, k, h)]][Q(x, k, h) := x[P(x, k, h)]])), b)
    <==> perm(a, b)

// a trace of steps that preserve the permutation, whose quantified side condition the simplifier decides once F is
// instantiated, e.g. by a lemma perm(F(b, k), c) <==> perm(b, c) on the step; for one and for two dependencies
// (from bubble_sort, insertion_sort)
lemma {:rw} {:teq} perm_steps(a: array<int, int>, c: array<int, int>, ks: List<int>, F: (array<int, int>, int) -> array<int, int>)
  requires forall b: array<int, int>, k: int :: perm(F(b, k), b)
  ensures perm(current(trace(a, for ks do b, k :: F(b, k))), c) <==> perm(a, c)

lemma {:rw} {:teq} perm_steps_two(a: array<int, int>, c: array<int, int>, ks: List<int>, is: List<int>,
                                  F: (array<int, int>, int, int) -> array<int, int>)
  requires forall b: array<int, int>, k: int, i: int :: perm(F(b, k, i), b)
  ensures perm(current(trace(a, for ks, is do b, k, i :: F(b, k, i))), c) <==> perm(a, c)

// inductions: the invariant of the outer loop as a quantified side condition over the steps F, which the simplifier
// decides by step lemmas on the atoms; all steps of the trace must be constrained, hence the number of steps is
// exactly n, or the steps extend the prefix for all positions

// a growing sorted prefix partitioned from the rest: exactly n steps sort b[0..n)
// (from selection_sort)
lemma {:rw} {:teq} sorted_prefix_steps(a: array<int, int>, n: int, m: Nat, F: (array<int, int>, int) -> array<int, int>)
  requires n == integer(m)
  requires forall b: array<int, int>, k: int :: 0 <= k < n && sorted(b, 0, k) && partitioned(b, 0, k, n)
    ==> sorted(F(b, k), 0, k + 1) && partitioned(F(b, k), 0, k + 1, n)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋ do b, k :: F(b, k))), 0, n) <==> true

// a growing sorted prefix from one element, the steps at the positions i of a second counter from 1 extending the
// sorted prefix b[0..i) by i for all i, hence m steps sort b[0..m + 1) and b[0..n) if n <= m + 1
// (from insertion_sort)
lemma {:rw} {:teq} sorted_prefix_steps_two(a: array<int, int>, n: int, m: Nat, F: (array<int, int>, int, int) -> array<int, int>)
  requires n <= integer(m) + 1
  requires forall b: array<int, int>, k: int, i: int :: 0 <= i && sorted(b, 0, i) ==> sorted(F(b, k, i), 0, i + 1)
  ensures sorted(current(trace(a, for ⌊counter(0, 1, m)⌋, ⌊counter(1, 1, m)⌋ do b, k, i :: F(b, k, i))), 0, n)
    <==> true
