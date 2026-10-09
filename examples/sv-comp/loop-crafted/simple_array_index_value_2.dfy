// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-crafted/simple_array_index_value_2.dfy
// SV-COMP ReachSafety-Loops/loop-crafted/simple_array_index_value_2.yml (expected: safe), translated from the C
// program by hand: each element is an arbitrary value above its index, which is checked; unsigned in C, which the
// assumption implies
//
// findings: the iteration constraint of the first loop, the arbitrary value of each iteration exceeds the
// iteration, is abstracted by the auxiliary predicate above, and instantiated at the positions of the assertions by
// the atom j < earlier(j, ts) (see standard_find_ground-1); closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 10000

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀

// the first n values of ts exceed their positions, an auxiliary predicate, which is not defined
predicate above(n: int, ts: seq<int>)

// the iteration constraint that the value of each iteration exceeds the iteration is abstracted by above, which is
// instantiated at the positions j in the range by the atom j < earlier(j, ts), the left-hand side
lemma {:rw} {:free} {:teq} forall n: int, ts: seq<int>, hs: seq<int> ::
  invs(for ⌊counter(0, 1, n)⌋, hs, ts check k, h, t :: k < t) <==> above(n, ts)
lemma {:rw} {:free} {:teq} forall n: int, j: int, ts: seq<int> ::
  if above(n, ts) && 0 <= j < n
  then (j < earlier(j, ts)) <==> true

method main() {
  var N: int;
  var array: array<int, int>;
  var index: int;
  var tmp: int;
  assume 0 < N;
  index := 0;
  while index < N {
    tmp := *;
    assume tmp > index;
    array := array[index := tmp];
    index := index + 1;
  }
  index := 0;
  while index < N {
    assert array[index] > index;
    index := index + 1;
  }
}

// remaining goals of -teq -simplify:
// none
