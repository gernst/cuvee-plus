// ./Cuvee.sh examples/dafny/teq/bsearch.dfy
// experiment: binary search with partition points, for -teq -split -simplify (see ideas/binary-search.md);
// the comparisons of the array with x are those of the indices with the partition points p and q,
// a[m] < x iff m < p, x < a[m] iff q <= m, a[m] == x iff p <= m < q, given by lemmas on global constants,
// such that the rules need no variables for the array, the bound, and x;
// this assumes partition points for all indices, which is stronger than sortedness of a[0..n)
// (all elements of a sorted array may be below x, then no index p exists)
//
// status: verified with -teq -split -simplify, given the cut after the loop;
// the traces of lo and hi are abstracted by incs and decs, monotonically increasing and decreasing values with
// the bounds p and q, which are bound by matching the guards (see Rewrite.conjuncts); the increase and decrease
// follow from the guards together with the loop test lo < hi, which holds in the updates (see Simplify.invariants),
// where the matching decides guards in the context of the update (see Rewrite.matches);
// the bounds lo <= p and q <= hi are proved at the cut by the lemmas on incs and decs, and then assumed,
// which closes the exit when x is not found with hi <= lo and p <= k < q for a[k] == x;
// the equations Lo == incs(..., ⌊Hi⌋, ...) and Hi == decs(..., ⌊Lo⌋, ...) depend on each other, which the matching
// follows (Ctx.↑), since cycles among the equations are only excluded where a solution is inlined (Simplify.poly);
// without the cut, one goal remains, as the bounds are facts about the terms current(incs(0, p, ...)) and
// current(decs(n, q, ...)), which the simplifier does not derive (see doc/simplifier.md);
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
lemma {:rw} lemma_1(m: int)
  ensures (a[m] < x) <==> m < p
lemma {:rw} lemma_2(m: int)
  ensures (x < a[m]) <==> q <= m
lemma {:rw} lemma_3(m: int)
  ensures (a[m] == x) <==> p <= m && m < q

// the declarations of teq.dfy that the lemmas refer to are repeated here, since Trace exists only with -teq
type Trace<a₀>
type List<a₀>
type Nat
function counter(x₀: int, x₁: int, x₂: Nat): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// a value that increases monotonically up to a bound b: in each iteration, it either keeps its value, case C,
// or increases to F(x, h) under the guard D(x, h) && x < F(x, h) && F(x, h) <= b, where D is bound to the whole guard
// of the program, the bound b by matching F(x, h) <= b against a conjunct of the guard, and the increase must follow
// from the guard (see Rewrite.guard)
function incs(x0: int, b: int, ks: List<int>, hs: List<int>,
              D: (int, int) -> bool, C: (int, int) -> bool, F: (int, int) -> int): Trace<int>

lemma {:rw} trace_1(x0: int, b: int, i: int, c: int, m: Nat, hs: List<int>, C: (int, int) -> bool,
                    D: (int, int) -> bool, F: (int, int) -> int)
  ensures trace(x0, for ⌊counter(i, c, m)⌋, hs do x, k, h ::
          case C(x, h) => x case D(x, h) && x < F(x, h) && F(x, h) <= b => F(x, h))
    == incs(x0, b, ⌊counter(i, c, m)⌋, hs, D, C, F)

// a value that decreases monotonically down to a bound b, dually
function decs(x0: int, b: int, ks: List<int>, ls: List<int>,
              D: (int, int) -> bool, C: (int, int) -> bool, F: (int, int) -> int): Trace<int>

lemma {:rw} trace_2(x0: int, b: int, i: int, c: int, m: Nat, ls: List<int>, C: (int, int) -> bool,
                    D: (int, int) -> bool, F: (int, int) -> int)
  ensures trace(x0, for ⌊counter(i, c, m)⌋, ls do x, k, l ::
          case C(x, l) => x case D(x, l) && F(x, l) < x && b <= F(x, l) => F(x, l))
    == decs(x0, b, ⌊counter(i, c, m)⌋, ls, D, C, F)

// the midpoint lies in the interval, for division that rounds down, which the simplifier does not know otherwise,
// needed for the increase lo < (hi + lo) / 2 + 1 and the decrease (hi + lo) / 2 < hi
lemma {:rw} lemma_4(l: int, h: int)
  requires l <= h
  ensures (l <= (h + l) / 2) <==> true
lemma {:rw} lemma_5(l: int, h: int)
  requires l < h
  ensures ((h + l) / 2 < h) <==> true


// the value stays below the bound if the initial value does
lemma current_1(x0: int, b: int, ks: List<int>, hs: List<int>, D: (int, int) -> bool, C: (int, int) -> bool,
                F: (int, int) -> int)
  requires x0 <= b
  ensures (current(incs(x0, b, ks, hs, D, C, F)) <= b) <==> true

// the value stays above the bound if the initial value does
lemma current_2(x0: int, b: int, ks: List<int>, ls: List<int>, D: (int, int) -> bool, C: (int, int) -> bool,
                F: (int, int) -> int)
  requires b <= x0
  ensures (b <= current(decs(x0, b, ks, ls, D, C, F))) <==> true


function incs_(x0: int, b: int, ks: List<int>, hs: List<int>,
              D: (int, int) -> bool, C: (int, int) -> bool, F: (int, int) -> int): Trace<int>

lemma {:rw} incs_1(X: Trace<int>, x0: int, b: int, i: int, c: int, m: Nat, hs: List<int>, C: (int, int) -> bool,
                   D: (int, int) -> bool, F: (int, int) -> int)
  ensures X == incs(x0, b, ⌊counter(i, c, m)⌋, hs, D, C, F)
    <==> X == incs_(x0, b, ⌊counter(i, c, m)⌋, hs, D, C, F) && current(X) <= b


function decs_(x0: int, b: int, ks: List<int>, ls: List<int>,
              D: (int, int) -> bool, C: (int, int) -> bool, F: (int, int) -> int): Trace<int>

lemma {:rw} decs_1(X: Trace<int>, x0: int, b: int, i: int, c: int, m: Nat, ls: List<int>, C: (int, int) -> bool,
                   D: (int, int) -> bool, F: (int, int) -> int)
  ensures X == decs(x0, b, ⌊counter(i, c, m)⌋, ls, D, C, F)
    <==> X == decs_(x0, b, ⌊counter(i, c, m)⌋, ls, D, C, F) && b <= current(X)

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
  // a cut, until facts about terms are derived (see doc/simplifier.md): the bounds are proved by the lemmas on
  // incs and decs, whose atoms occur here, and then assumed for the postcondition, since -teq does not assume
  // assertions
  // assert lo <= p && q <= hi;
  // assume lo <= p && q <= hi;
}
