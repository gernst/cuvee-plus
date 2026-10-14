// ./Cuvee.sh -teq -prove examples/dafny/state/bsearch.dfy
// binary search, after examples/dafny/teq/bsearch.dfy (see doc/prove.md), with constant partition points;
// kept as a regression test of the per-component abstractions (see doc/prove.md)
//
// the array is given by partition points p and q instead of sortedness: a[m] < x below p, a[m] == x between p and q,
// and x < a[m] from q on, such that the rules need no variables for the array, the bound, and x; this is stronger
// than sortedness of a[0..n), whose elements may all be below x
//
// lo and hi read each other and form one trace of two accumulators, S; the view of each component is a single trace
// over the history of the other one, which trace_1 and trace_2 abstract by incs and decs, a value that increases up
// to p and one that decreases down to q; the bounds of these, current_1 and current_2, are forward facts that fire at
// current(S).0 and current(S).1, which closes the exit with hi <= lo and p <= k < q; the found case closes by the test
// of the branch with break, and i keeps -1 on the exit

const a: array<int, int>
const n: int
const x: int
const p: int
const q: int

// the reads of the array as comparisons of the index with the partition points, such that the guards a[mid] < x and
// x < a[mid] become mid < p and q <= mid, and a[k] == x of the postcondition becomes p <= k < q
lemma {:rw} lemma_1(m: int)
  ensures (a[m] < x) <==> m < p

lemma {:rw} lemma_2(m: int)
  ensures (x < a[m]) <==> q <= m

lemma {:rw} lemma_3(m: int)
  ensures (a[m] == x) <==> p <= m && m < q

// a value that increases monotonically up to a bound b: in each iteration, it either keeps its value, case C, or
// increases to F(x, h) under the guard D(x, h) && x < F(x, h) <= b, where D is bound to the whole guard, b by matching
// F(x, h) <= b against a conjunct of the guard, and the increase must follow from the guard (the midpoint by the
// bounds of division in the linear arithmetic, l <= (h + l) / 2 < h for l < h); polymorphic in the other
// dependency, the history of the other component
function incs<a>(x0: int, b: int, ks: List<int>, hs: List<a>,
              D: (int, a) -> bool, C: (int, a) -> bool, F: (int, a) -> int): Trace<int>

lemma {:rw} trace_1<a>(x0: int, b: int, i: int, c: int, m: Nat, hs: List<a>, C: (int, a) -> bool,
                    D: (int, a) -> bool, F: (int, a) -> int)
  ensures trace(x0, for ⌊counter(i, c, m)⌋, hs do x, k, h ::
          case C(x, h) => x case D(x, h) && x < F(x, h) && F(x, h) <= b => F(x, h))
    == incs(x0, b, ⌊counter(i, c, m)⌋, hs, D, C, F)

// the value stays below the bound if the initial value does
lemma {:fw} current_1<a>(x0: int, b: int, ks: List<int>, hs: List<a>, D: (int, a) -> bool, C: (int, a) -> bool,
                F: (int, a) -> int)
  requires x0 <= b
  ensures current(incs(x0, b, ks, hs, D, C, F)) <= b

// a value that decreases monotonically down to a bound b, dually
function decs<a>(x0: int, b: int, ks: List<int>, ls: List<a>,
              D: (int, a) -> bool, C: (int, a) -> bool, F: (int, a) -> int): Trace<int>

lemma {:rw} trace_2<a>(x0: int, b: int, i: int, c: int, m: Nat, ls: List<a>, C: (int, a) -> bool,
                    D: (int, a) -> bool, F: (int, a) -> int)
  ensures trace(x0, for ⌊counter(i, c, m)⌋, ls do x, k, l ::
          case C(x, l) => x case D(x, l) && F(x, l) < x && b <= F(x, l) => F(x, l))
    == decs(x0, b, ⌊counter(i, c, m)⌋, ls, D, C, F)

// the value stays above the bound if the initial value does
lemma {:fw} current_2<a>(x0: int, b: int, ks: List<int>, ls: List<a>, D: (int, a) -> bool, C: (int, a) -> bool,
                F: (int, a) -> int)
  requires b <= x0
  ensures b <= current(decs(x0, b, ks, ls, D, C, F))

method search() returns (i: int)
  requires 0 <= p <= q <= n
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
