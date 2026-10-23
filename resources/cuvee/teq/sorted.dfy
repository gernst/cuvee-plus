// sorting: the abstract predicates sorted, perm (permutation as a total map on the indices, so that a swap at any
// two positions preserves it) and partitioned, with the generic lemmas on traces of swaps and of steps, the inductions
// for sorting by a growing sorted prefix, with the invariant as a quantified side condition decided by step lemmas on
// atoms, and the partition points of a sorted array, which turn its reads into comparisons of indices; an optional
// module over teq.dfy alone (-include teq:sorted; the cuts of its comparisons are those of the bisection of
// teq:search), migrated on Oct 13, 2026 from
// sorting.dfy of the per-variable form, with the partition points of examples/dafny/algorithms/bsearch.dfy; the
// algorithms' own knowledge (summaries of inner loops, step lemmas) stays with the examples; the predicates and the
// partition points are defined here (the proofs of the lemmas in lean/ use the definitions), but the engines use
// the lemmas only, the definitions are no rules; no task of SV-COMP uses them (the results since Oct 13, 2026), they
// serve the examples of examples/dafny/algorithms

// a[lo..hi) is nondecreasing; the bounds are integers, as the indices of the programs, like those of cut
function {:teq} sorted(a: array<int, int>, lo: int, hi: int): bool
{
  forall i: int, j: int :: lo <= i && i <= j && j < hi ==> a[i] <= a[j]
}

// a is a permutation of b as a total map on the indices: b read through a bijection f of the indices, whose inverse
// is g
function {:teq} perm(a: array<int, int>, b: array<int, int>): bool
{
  exists f: int -> int, g: int -> int ::
    (forall i: int :: g(f(i)) == i) && (forall i: int :: f(g(i)) == i) && (forall i: int :: a[i] == b[f(i)])
}

// all of a[lo..mid) are at most all of a[mid..hi)
function {:teq} partitioned(a: array<int, int>, lo: int, mid: int, hi: int): bool
{
  forall i: int, j: int :: lo <= i && i < mid && mid <= j && j < hi ==> a[i] <= a[j]
}

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
lemma {:rw} {:teq} sorted_adjacent(a: array<int, int>, n: Nat)
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

// the partition points of a sorted array a[0..len): below lower(ar, len, y), the elements are less than y, from
// upper(ar, len, y) on, greater; the cuts of the comparisons with y
function {:teq} lower(ar: array<int, int>, len: int, y: int): int
{
  cut((j: int) => ar[j] < y, 0, len)
}

function {:teq} upper(ar: array<int, int>, len: int, y: int): int
{
  cut((j: int) => ar[j] <= y, 0, len)
}

lemma {:rw} {:teq} lower(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, 0, len) && 0 <= m && m < len
  ensures (ar[m] < y) <==> m < lower(ar, len, y)

lemma {:rw} {:teq} upper(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, 0, len) && 0 <= m && m < len
  ensures (y < ar[m]) <==> upper(ar, len, y) <= m

lemma {:rw} {:teq} lower_le(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, 0, len) && 0 <= m && m < len
  ensures (y <= ar[m]) <==> lower(ar, len, y) <= m

lemma {:rw} {:teq} equal(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, 0, len) && 0 <= m && m < len
  ensures (ar[m] == y) <==> lower(ar, len, y) <= m && m < upper(ar, len, y)

// the partition points lie within the bounds, where they occur (the exit, P <= Q, and the found case, Q <= n)
lemma {:fw} {:teq} bounds(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, 0, len) && 0 <= len
  ensures 0 <= lower(ar, len, y) && lower(ar, len, y) <= upper(ar, len, y) && upper(ar, len, y) <= len

// the cut of the comparison with y on a sorted array is its partition point; the negation of the other guard,
// !(y < ar[j]), is ar[j] <= y, which is ar[j] < y + 1 on Int, whose partition point is upper(ar, len, y)
lemma {:rw} {:teq} cut_lower(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, 0, len) && 0 <= len
  ensures cut((j: int) => ar[j] < y, 0, len) == lower(ar, len, y)

lemma {:rw} {:teq} lower_succ(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, 0, len)
  ensures lower(ar, len, y + 1) == upper(ar, len, y)
