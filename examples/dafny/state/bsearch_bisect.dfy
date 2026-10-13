// ./Cuvee.sh -teq-state -prove examples/dafny/state/bsearch_bisect.dfy
// the binary search over a sorted array of bsearch_sorted.dfy, proved by a lemma over the whole cycle instead of two
// layers (package O of ideas/deduction-engine-plan.md): the array, its bound and the key are parameters, the array
// is sorted, sorted(a, n)
//
// sortedness is used where the reads of the array become comparisons of the index with the partition points
// lower(a, n, y) and upper(a, n, y), which exist for a sorted array (lower_def, upper_def, equal_def), for indices
// within a[0..n) only; lo and hi read each other and form one trace S of two accumulators, which the lemmas
// bisect_1 and bisect_2 abstract as a whole: a bisection of [l0, h0) whose guards G and H hold on a prefix and a
// suffix keeps lo below the cut of G and hi above that of H (forward facts at current(S).0 and current(S).1); the
// conditions are decided by the rules on sortedness within the range of their premise, and the cuts of the
// comparisons with x are the partition points (cut_lower, cut_upper); the midpoint (h + l) / 2 is bounded by the
// linear arithmetic

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

// the partition points lie within the bounds, where they occur (the exit, P <= Q, and the found case, Q <= n)
lemma {:fw} bounds(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures 0 <= lower(ar, len, y) && lower(ar, len, y) <= upper(ar, len, y) && upper(ar, len, y) <= len

// the cut of a predicate G that holds on a prefix of [l, h): the first index where it fails, h if none; and the cut
// of a predicate H that holds on a suffix: the first index where it holds, h if none
function cut(G: int -> bool, l: int, h: int): int

function cut2(H: int -> bool, l: int, h: int): int

// the cuts of the comparisons with y on a sorted array are its partition points
lemma {:rw} cut_lower(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures cut((j: int) => ar[j] < y, 0, len) == lower(ar, len, y)

lemma {:rw} cut_upper(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures cut2((j: int) => y < ar[j], 0, len) == upper(ar, len, y)

// a bisection of [l0, h0): while lo < hi, the midpoint moves lo above it where G holds and hi down to it where H
// holds; if G holds on a prefix of [l0, h0), lo stays within l0 and the cut of G, and if H holds on a suffix, hi
// stays within the cut of H and h0; the guards are higher-order in the midpoint, bound to the guards of the program
// by abstraction, and lo < hi follows from the iteration constraint in the update
lemma {:fw} bisect_1(l0: int, h0: int, i: int, c: int, m: Nat, G: int -> bool, H: int -> bool)
  requires l0 <= h0
  requires forall p: int, q: int :: l0 <= p && p <= q && q < h0 && G(q) ==> G(p)
  ensures l0 <= current(trace(l0, h0, for ⌊counter(i, c, m)⌋ do lo, hi, k ::
          case G((hi + lo) / 2) && lo < hi => (hi + lo) / 2 + 1 case H((hi + lo) / 2) && lo < hi => lo,
          case G((hi + lo) / 2) && lo < hi => hi case H((hi + lo) / 2) && lo < hi => (hi + lo) / 2)).0
       <= cut(G, l0, h0)

lemma {:fw} bisect_2(l0: int, h0: int, i: int, c: int, m: Nat, G: int -> bool, H: int -> bool)
  requires l0 <= h0
  requires forall p: int, q: int :: l0 <= p && p <= q && q < h0 && H(p) ==> H(q)
  ensures cut2(H, l0, h0) <= current(trace(l0, h0, for ⌊counter(i, c, m)⌋ do lo, hi, k ::
          case G((hi + lo) / 2) && lo < hi => (hi + lo) / 2 + 1 case H((hi + lo) / 2) && lo < hi => lo,
          case G((hi + lo) / 2) && lo < hi => hi case H((hi + lo) / 2) && lo < hi => (hi + lo) / 2)).1
       <= h0

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
