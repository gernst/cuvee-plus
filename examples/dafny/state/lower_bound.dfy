// ./Cuvee.sh -teq-state -prove examples/dafny/state/lower_bound.dfy
// the lower bound of x in a sorted array, after examples/dafny/algorithms/lower_bound.dfy (open under -teq -simplify):
// the binary search without the found case, whose result is the partition point lower(a, n, x); proved with the
// bisection lemmas of bsearch_bisect.dfy (package O of ideas/deduction-engine-plan.md): the guard of the else branch,
// !(a[mid] < x), is normalized to x <= a[mid], whose cut is lower(a, n, x) as well (cut_le), and the reads of that
// form get their own rule (lower_le); the exit hi <= lo with lo <= lower(a, n, x) <= hi makes lo the partition point,
// which closes both quantified postconditions by the rules on sortedness

function sorted(ar: array<int, int>, len: int): bool

function lower(ar: array<int, int>, len: int, y: int): int

// the partition point of a sorted array: below lower(ar, len, y), the elements are less than y; the variables are
// named apart from those of the method, which they would capture
lemma {:rw} lower_def(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (ar[m] < y) <==> m < lower(ar, len, y)

lemma {:rw} lower_le(ar: array<int, int>, len: int, y: int, m: int)
  requires sorted(ar, len) && 0 <= m && m < len
  ensures (y <= ar[m]) <==> lower(ar, len, y) <= m

// the cut of a predicate G that holds on a prefix of [l, h): the first index where it fails, h if none; and the cut
// of a predicate H that holds on a suffix: the first index where it holds, h if none
function cut(G: int -> bool, l: int, h: int): int

function cut2(H: int -> bool, l: int, h: int): int

// the cuts of the comparisons with y on a sorted array are its partition point
lemma {:rw} cut_lower(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures cut((j: int) => ar[j] < y, 0, len) == lower(ar, len, y)

lemma {:rw} cut_le(ar: array<int, int>, len: int, y: int)
  requires sorted(ar, len) && 0 <= len
  ensures cut2((j: int) => y <= ar[j], 0, len) == lower(ar, len, y)

// a bisection of [l0, h0), as in bsearch_bisect.dfy
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
