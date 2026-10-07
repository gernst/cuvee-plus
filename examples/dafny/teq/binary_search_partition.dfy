// experiment: binary search with partition points, for -teq -split -simplify (see bsearch.md);
// the comparisons of the array with x are those of the indices with the partition points p and q,
// a[m] < x iff m < p, x < a[m] iff q <= m, a[m] == x iff p <= m < q, given by lemmas on global constants,
// such that the rules need no variables for the array, the bound, and x;
// this assumes partition points for all indices, which is stronger than sortedness of a[0..n)
// (all elements of a sorted array may be below x, then no index p exists)
//
// status: the trace of lo matches incs, a monotonically increasing value, see below;
// one goal remains, the exit when x is not found, which needs lo <= p and q <= hi,
// invariants of the traces of lo and hi, together with the exit hi <= lo and p <= k < q for a[k] == x;
// these are facts about the terms current(Lo) and current(Hi), which the rewriter does not derive (see forward.md),
// the comparisons would then be decided by the difference constraints of the context;
// the found case is closed by the test of the branch with break, mid < n and a[mid] == x from p <= mid < q <= n;
// the exit of the loop by its test closes once i is known to keep its value -1: the simplifier merges the cases
// of its update, which are all i, and the trace that keeps its value is consts(n, -1) by the lemma of teq.dfy

const a: array<int, int>
const n: int
const x: int
const p: int
const q: int

// the reads of the array become comparisons of the indices with the partition points: below p, a[m] is less
// than x, from q on, it is greater, and in between, it is x; the guards a[mid] < x and x < a[mid] of the loop
// become mid < p and q <= mid, and a[k] == x of the postcondition becomes p <= k < q
lemma {:rw} {:free} forall m: int :: (a[m] < x) <==> m < p
lemma {:rw} {:free} forall m: int :: (x < a[m]) <==> q <= m
lemma {:rw} {:free} forall m: int :: (a[m] == x) <==> p <= m && m < q

// the declarations of teq.dfy that the lemmas refer to are repeated here, since Trace exists only with -teq
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>

// a value that increases monotonically: in each iteration, it either keeps its value, case C, or increases,
// where the increase is part of the guard of the other case, x < F(x, h); the case that keeps the value is matched
// first, which binds C, such that the guard of the other case is instantiated and follows from that of the program;
// the cases are matched in the order of the program, hence its branches are swapped below
function incs(x0: int, ks: seq<int>, hs: seq<int>,
              B: (int, int) -> bool, C: (int, int) -> bool, F: (int, int) -> int): Trace<int>

lemma {:rw} {:free} forall x0: int, i: int, c: int, m: int, hs: seq<int>,
                          C: (int, int) -> bool, F: (int, int) -> int ::
  trace(x0, for ⌊counter(i, c, m)⌋, hs do x, k, h :: case C(x, h) => x case !C(x, h) && x < F(x, h) => F(x, h))
    == incs(x0, ⌊counter(i, c, m)⌋, hs, (x: int, h: int) => !C(x, h), C, F)

// the midpoint lies in the interval, for division that rounds down, which the simplifier does not know otherwise,
// needed for the increase lo < (hi + lo) / 2 + 1
lemma {:rw} {:free} forall l: int, h: int :: if l <= h then (l <= (h + l) / 2) <==> true

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
    // the loop test is repeated as a branch, such that it is part of the guards of the updates of the traces
    // (the test of the loop and assumptions in the body are recorded in invs only)
    if lo < hi {
      mid := (lo + hi) / 2;
      if x < a[mid] {
        hi := mid;
      } else if a[mid] < x {
        lo := mid + 1;
      } else {
        i := mid;
        break;
      }
    }
  }
}
