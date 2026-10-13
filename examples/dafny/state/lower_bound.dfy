// ./Cuvee.sh -teq -prove examples/dafny/state/lower_bound.dfy
// the lower bound of x in a sorted array, after examples/dafny/algorithms/lower_bound.dfy (open under -teq -simplify):
// the binary search without the found case, whose result is the partition point lower(a, n, x); proved with the
// named bisection of bsearch_bisect.dfy (package O of ideas/deduction-engine-plan.md): the guard of the else branch,
// !(a[mid] < x), is normalized to x <= a[mid], whose negation is a[mid] < x again, so its cut is lower(a, n, x) by
// cut_lower, and the reads of that form get their own rule (lower_le); the exit hi <= lo with
// lo <= lower(a, n, x) <= hi makes lo the partition point, which closes both quantified postconditions by the rules
// on sortedness

function sorted(ar: array<int, int>, len: int): bool

function lower(ar: array<int, int>, len: int, y: int): int

// the partition point of a sorted array: below lower(ar, len, y), the elements are less than y
lemma {:rw} lower(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (ar[m] < y) <==> m < lower(ar, len, y)

lemma {:rw} lower_le(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (y <= ar[m]) <==> lower(ar, len, y) <= m

// the cut of a predicate G that holds on a prefix of [l, h): the first index where it fails, h if none; a predicate
// H that holds on a suffix has the cut of its negation, the first index where H holds
function cut(G: int -> bool, l: int, h: int): int

// the cut of the comparison with y on a sorted array is its partition point; that of the guard of the else branch,
// x <= a[mid], is the same, since its negation is a[mid] < x
lemma {:rw} cut_lower(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures cut((j: int) => ar[j] < y, 0, len) == lower(ar, len, y)

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

method main(a: array<int, int>, n: int, x: int) returns (lo: int)
  requires 0 <= n
  requires sorted(a, n)
  ensures 0 <= lo <= n
  ensures forall k: int :: 0 <= k < lo ==> a[k] < x
  ensures forall k: int :: lo <= k < n ==> x <= a[k]
{
  var hi: int;
  var mid: int;
  lo := 0;
  hi := n;
  while lo < hi
  {
    mid := (lo + hi) / 2;
    if a[mid] < x {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
}
