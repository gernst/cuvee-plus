// ./Cuvee.sh -teq-state -prove examples/dafny/state/bsearch_bisect.dfy
// the binary search over a sorted array of bsearch_sorted.dfy, proved by a lemma over the whole cycle instead of two
// layers (package O of ideas/deduction-engine-plan.md): the array, its bound and the key are parameters, the array
// is sorted, sorted(a, n)
//
// sortedness is used where the reads of the array become comparisons of the index with the partition points
// lower(a, n, y) and upper(a, n, y), which exist for a sorted array, for indices within a[0..n) only; lo and hi read
// each other and form one trace S of two accumulators, which the rule bisection names: a bisection of [l0, h0) with
// a probe strictly inside the interval, (lo + hi) / 2 here; if its guards G and H hold on a prefix and a suffix, lo
// stays below the cut of G and hi above the cut of the negation of H (bisection_lo, bisection_hi, forward facts at
// current(S).0 and current(S).1); the conditions are decided by the rules on sortedness within the range of their
// premise and, for the probe, by the bounds of division in the linear arithmetic; the cuts of the comparisons with x
// are the partition points (cut_lower, lower_succ)

function sorted(ar: array<int, int>, len: int): bool

function lower(ar: array<int, int>, len: int, y: int): int

function upper(ar: array<int, int>, len: int, y: int): int

// the partition points of a sorted array: below lower(ar, len, y), the elements are less than y, from
// upper(ar, len, y) on, greater
lemma {:rw} lower(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (ar[m] < y) <==> m < lower(ar, len, y)

lemma {:rw} upper(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (y < ar[m]) <==> upper(ar, len, y) <= m

lemma {:rw} equal(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (ar[m] == y) <==> lower(ar, len, y) <= m && m < upper(ar, len, y)

// the partition points lie within the bounds, where they occur (the exit, P <= Q, and the found case, Q <= n)
lemma {:fw} bounds(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures 0 <= lower(ar, len, y) && lower(ar, len, y) <= upper(ar, len, y) && upper(ar, len, y) <= len

// the cut of a predicate G that holds on a prefix of [l, h): the first index where it fails, h if none; a predicate
// H that holds on a suffix has the cut of its negation, the first index where H holds
function cut(G: int -> bool, l: int, h: int): int

// the cut of the comparison with y on a sorted array is its partition point; the negation of the other guard,
// !(y < ar[j]), is ar[j] <= y, which is ar[j] < y + 1 on Int, whose partition point is upper(ar, len, y)
lemma {:rw} cut_lower(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures cut((j: int) => ar[j] < y, 0, len) == lower(ar, len, y)

lemma {:rw} lower_succ(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len)
  ensures lower(ar, len, y + 1) == upper(ar, len, y)

// a bisection of [l0, h0) with a probe M strictly inside the interval: while lo < hi, lo moves above the probe where
// G holds and hi down to it where H holds; named by bisection, which keeps the probe and the guards
function bisection(l0: int, h0: int, ks: List<int>, M: (int, int) -> int, G: int -> bool,
                   H: int -> bool): Trace<(int, int)>

lemma {:rw} bisection(l0: int, h0: int, i: int, c: int, m: Nat, M: (int, int) -> int, G: int -> bool,
                      H: int -> bool)
  ensures trace(l0, h0, for ⌊counter(i, c, m)⌋ do lo, hi, k ::
          case G(M(lo, hi)) && lo < hi => M(lo, hi) + 1 case H(M(lo, hi)) && lo < hi => lo,
          case G(M(lo, hi)) && lo < hi => hi case H(M(lo, hi)) && lo < hi => M(lo, hi))
    == bisection(l0, h0, ⌊counter(i, c, m)⌋, M, G, H)

// if G holds on a prefix of [l0, h0), lo stays within l0 and the cut of G, and if H holds on a suffix, hi stays within
// the cut of its negation and h0
lemma {:fw} bisection_lo(l0: int, h0: int, ks: List<int>, M: (int, int) -> int, G: int -> bool, H: int -> bool)
  requires l0 <= h0
  requires forall l: int, h: int :: l < h ==> l <= M(l, h) && M(l, h) < h
  requires forall p: int, q: int :: l0 <= p && p <= q && q < h0 && G(q) ==> G(p)
  ensures l0 <= current(bisection(l0, h0, ks, M, G, H)).0 <= cut(G, l0, h0)

lemma {:fw} bisection_hi(l0: int, h0: int, ks: List<int>, M: (int, int) -> int, G: int -> bool, H: int -> bool)
  requires l0 <= h0
  requires forall l: int, h: int :: l < h ==> l <= M(l, h) && M(l, h) < h
  requires forall p: int, q: int :: l0 <= p && p <= q && q < h0 && H(p) ==> H(q)
  ensures cut((j: int) => !H(j), l0, h0) <= current(bisection(l0, h0, ks, M, G, H)).1 <= h0

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
