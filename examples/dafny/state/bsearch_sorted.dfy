// ./Cuvee.sh -teq-state -prove examples/dafny/state/bsearch_sorted.dfy
// the binary search of bsearch.dfy over a sorted array: the array, its bound and the key are parameters, the array
// is sorted, sorted(a, n), instead of given by partition points (step 2b of ideas/deduction-engine-implementation.md)
//
// sortedness is used once, where the reads of the array become comparisons of the index with the partition points
// lower(a, n, y) and upper(a, n, y), which exist for a sorted array (lower_def, upper_def, equal_def); these hold only
// for indices within a[0..n), so the guards a[mid] < x and x < a[mid] in the update of the loop are rewritten only
// once 0 <= lo and hi <= n are known there, as invariants over the histories of lo and hi; these follow from the
// monotonicity of each component (up_1, down_1, forward lemmas whose trigger is the history ⌊S⌋.i, matched through
// its view), after which the views match incs and decs with the partition points as bounds, as in bsearch.dfy
//
// interim: the invariant is a joint one, 0 <= lo <= lower, upper <= hi <= n, and is built here in two layers, which
// costs (about 45 s against 7 s for bsearch.dfy); a single lemma over the trace of both accumulators is planned
// (package O of ideas/deduction-engine-plan.md); the midpoint (h + l) / 2 is bounded by the linear arithmetic

function sorted(ar: array<int, int>, len: int): bool

function lower(ar: array<int, int>, len: int, y: int): int

function upper(ar: array<int, int>, len: int, y: int): int

// the partition points of a sorted array: below lower(ar, len, y), the elements are less than y, from
// upper(ar, len, y) on, greater; the variables are named apart from those of the method, which they would capture
lemma {:rw} lower_def(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (ar[m] < y) <==> m < lower(ar, len, y)

lemma {:rw} upper_def(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (y < ar[m]) <==> upper(ar, len, y) <= m

lemma {:rw} equal_def(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (ar[m] == y) <==> lower(ar, len, y) <= m && m < upper(ar, len, y)

// the partition points lie within the bounds, as atoms of conditions (the initial values of incs and decs) and as
// facts where they occur (the found case, i < n by mid < upper <= n)
lemma {:rw} lower_bound(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures (0 <= lower(ar, len, y)) <==> true

lemma {:rw} upper_bound(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures (upper(ar, len, y) <= len) <==> true

lemma {:fw} bounds(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures 0 <= lower(ar, len, y) && lower(ar, len, y) <= upper(ar, len, y) && upper(ar, len, y) <= len

// monotone values, without a bound: all values of the history and the current value stay above (below) the initial
// one, where the increase (decrease) follows from the guard
lemma {:fw} up_1<a>(x0: int, i: int, c: int, m: Nat, hs: List<a>, C: (int, a) -> bool,
                    D: (int, a) -> bool, F: (int, a) -> int)
  ensures invs(for ⌊trace(x0, for ⌊counter(i, c, m)⌋, hs do v, k, h ::
          case C(v, h) => v case D(v, h) && v < F(v, h) => F(v, h))⌋ check w :: x0 <= w)

lemma {:fw} up_2<a>(x0: int, i: int, c: int, m: Nat, hs: List<a>, C: (int, a) -> bool,
                    D: (int, a) -> bool, F: (int, a) -> int)
  ensures x0 <= current(trace(x0, for ⌊counter(i, c, m)⌋, hs do v, k, h ::
          case C(v, h) => v case D(v, h) && v < F(v, h) => F(v, h)))

lemma {:fw} down_1<a>(x0: int, i: int, c: int, m: Nat, ls: List<a>, C: (int, a) -> bool,
                      D: (int, a) -> bool, F: (int, a) -> int)
  ensures invs(for ⌊trace(x0, for ⌊counter(i, c, m)⌋, ls do v, k, l ::
          case C(v, l) => v case D(v, l) && F(v, l) < v => F(v, l))⌋ check w :: w <= x0)

lemma {:fw} down_2<a>(x0: int, i: int, c: int, m: Nat, ls: List<a>, C: (int, a) -> bool,
                      D: (int, a) -> bool, F: (int, a) -> int)
  ensures current(trace(x0, for ⌊counter(i, c, m)⌋, ls do v, k, l ::
          case C(v, l) => v case D(v, l) && F(v, l) < v => F(v, l))) <= x0

// a value that increases monotonically up to a bound b, and one that decreases down to b, as in bsearch.dfy
function incs<a>(x0: int, b: int, ks: List<int>, hs: List<a>,
              D: (int, a) -> bool, C: (int, a) -> bool, F: (int, a) -> int): Trace<int>

lemma {:rw} trace_1<a>(x0: int, b: int, i: int, c: int, m: Nat, hs: List<a>, C: (int, a) -> bool,
                    D: (int, a) -> bool, F: (int, a) -> int)
  ensures trace(x0, for ⌊counter(i, c, m)⌋, hs do v, k, h ::
          case C(v, h) => v case D(v, h) && v < F(v, h) && F(v, h) <= b => F(v, h))
    == incs(x0, b, ⌊counter(i, c, m)⌋, hs, D, C, F)

lemma {:fw} current_1<a>(x0: int, b: int, ks: List<int>, hs: List<a>, D: (int, a) -> bool, C: (int, a) -> bool,
                F: (int, a) -> int)
  requires x0 <= b
  ensures current(incs(x0, b, ks, hs, D, C, F)) <= b

function decs<a>(x0: int, b: int, ks: List<int>, ls: List<a>,
              D: (int, a) -> bool, C: (int, a) -> bool, F: (int, a) -> int): Trace<int>

lemma {:rw} trace_2<a>(x0: int, b: int, i: int, c: int, m: Nat, ls: List<a>, C: (int, a) -> bool,
                    D: (int, a) -> bool, F: (int, a) -> int)
  ensures trace(x0, for ⌊counter(i, c, m)⌋, ls do v, k, l ::
          case C(v, l) => v case D(v, l) && F(v, l) < v && b <= F(v, l) => F(v, l))
    == decs(x0, b, ⌊counter(i, c, m)⌋, ls, D, C, F)

lemma {:fw} current_2<a>(x0: int, b: int, ks: List<int>, ls: List<a>, D: (int, a) -> bool, C: (int, a) -> bool,
                F: (int, a) -> int)
  requires b <= x0
  ensures b <= current(decs(x0, b, ks, ls, D, C, F))

method search(a: array<int, int>, n: int, x: int) returns (i: int)
  requires 0 <= n && sorted(a, n)
  ensures 0 <= i ==> i < n && a[i] == x
  ensures i < 0 ==> forall k: int :: 0 <= k < n ==> a[k] != x
{
  var lo: int;
  var hi: int;
  var mid: int;
  lo := 0;
  hi := n;
  i := -1;
  while lo < hi
  {
    mid := (lo + hi) / 2;
    if a[mid] < x {
      lo := mid + 1;
    } else if x < a[mid] {
      hi := mid;
    } else {
      i := mid;
      break;
    }
  }
}
