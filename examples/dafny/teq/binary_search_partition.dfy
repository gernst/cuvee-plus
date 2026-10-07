// experiment: binary search with partition points, for -teq -split -simplify (see bsearch.md);
// the comparisons of the array with x are those of the indices with the partition points p and q,
// a[m] < x iff m < p, x < a[m] iff q <= m, a[m] == x iff p <= m < q, given by lemmas on global constants,
// such that the rules need no variables for the array, the bound, and x;
// this assumes partition points for all indices, which is stronger than sortedness of a[0..n)
// (all elements of a sorted array may be below x, then no index p exists)
//
// status: verified with -teq -split -simplify, given the cut after the loop;
// the traces of lo and hi are abstracted by incs and decs, monotonically increasing and decreasing values,
// whose bounds lo <= p and q <= hi are proved at the cut by the lemmas on incs and decs, and then assumed,
// which closes the exit when x is not found with hi <= lo and p <= k < q for a[k] == x;
// the equations Lo == incs(..., ⌊Hi⌋, ...) and Hi == decs(..., ⌊Lo⌋, ...) depend on each other, which the matching
// follows (Ctx.↑), since cycles among the equations are only excluded where a replacement is applied (Simplify.var_);
// without the cut, one goal remains, as the bounds are facts about terms, which the rewriter does not derive
// (see forward.md);
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
function current<a₀>(x₀: Trace<a₀>): a₀

// a value that increases monotonically: in each iteration, it either keeps its value, case C, or changes to F(x, h)
// under the guard D(x, h), where the guard of the program is bound as a whole, and the increase x < F(x, h) is a
// condition, decided once C, D, and F are bound
function incs(x0: int, ks: seq<int>, hs: seq<int>,
              D: (int, int) -> bool, C: (int, int) -> bool, F: (int, int) -> int): Trace<int>

lemma {:rw} {:free} forall x0: int, i: int, c: int, m: int, hs: seq<int>,
                          C: (int, int) -> bool, D: (int, int) -> bool, F: (int, int) -> int ::
  if forall x: int, h: int :: D(x, h) ==> x < F(x, h)
  then trace(x0, for ⌊counter(i, c, m)⌋, hs do x, k, h :: case C(x, h) => x case D(x, h) => F(x, h))
         == incs(x0, ⌊counter(i, c, m)⌋, hs, D, C, F)

// the value stays below every bound of the initial value and of each change
lemma {:rw} {:free} forall x0: int, ks: seq<int>, hs: seq<int>,
                          D: (int, int) -> bool, C: (int, int) -> bool, F: (int, int) -> int, b: int ::
  if x0 <= b && (forall x: int, h: int :: D(x, h) ==> F(x, h) <= b)
  then (current(incs(x0, ks, hs, D, C, F)) <= b) <==> true

// a value that decreases monotonically, dually
function decs(x0: int, ks: seq<int>, ls: seq<int>,
              D: (int, int) -> bool, C: (int, int) -> bool, F: (int, int) -> int): Trace<int>

lemma {:rw} {:free} forall x0: int, i: int, c: int, m: int, ls: seq<int>,
                          C: (int, int) -> bool, D: (int, int) -> bool, F: (int, int) -> int ::
  if forall x: int, l: int :: D(x, l) ==> F(x, l) < x
  then trace(x0, for ⌊counter(i, c, m)⌋, ls do x, k, l :: case C(x, l) => x case D(x, l) => F(x, l))
         == decs(x0, ⌊counter(i, c, m)⌋, ls, D, C, F)

// the value stays above every bound of the initial value and of each change
lemma {:rw} {:free} forall x0: int, ks: seq<int>, ls: seq<int>,
                          D: (int, int) -> bool, C: (int, int) -> bool, F: (int, int) -> int, b: int ::
  if b <= x0 && (forall x: int, l: int :: D(x, l) ==> b <= F(x, l))
  then (b <= current(decs(x0, ks, ls, D, C, F))) <==> true

// the midpoint lies in the interval, for division that rounds down, which the simplifier does not know otherwise,
// needed for the increase lo < (hi + lo) / 2 + 1 and the decrease (hi + lo) / 2 < hi
lemma {:rw} {:free} forall l: int, h: int :: if l <= h then (l <= (h + l) / 2) <==> true
lemma {:rw} {:free} forall l: int, h: int :: if l < h then ((h + l) / 2 < h) <==> true

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
  // a cut, until facts about terms are derived (see forward.md): the bounds are proved by the lemmas on incs and decs,
  // whose atoms occur here, and then assumed for the postcondition, since -teq does not assume assertions
  assert lo <= p && q <= hi;
  assume lo <= p && q <= hi;
}
