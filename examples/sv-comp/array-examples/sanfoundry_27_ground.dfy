// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/sanfoundry_27_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/sanfoundry_27_ground.yml (expected: safe), translated from the C program by hand:
// the largest element of an arbitrary array, starting from array[0], is checked to be at least each element
//
// findings: teq.dfy summarizes the maximum as maxs over the elements read at the counter from 1, with the element
// at 0 as its initial value; a lemma, a variant of the bound of teq.dfy for maxs, states that it is at least each
// of the elements at 0, ..., m, with the comparison as its left-hand side; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀
function maxs(x: int, values: seq<int>): Trace<int>

// the maximum of the element at 0 and the elements at 1, ..., m read in the iterations is at least each of the
// elements at 0, ..., m; the left-hand side is a comparison
lemma {:rw} {:free} {:teq} forall xs: seq<int>, m: int, j: int ::
  if 0 <= j <= m
  then earlier(j, xs) <= current(maxs(earlier(0, xs), maps(for ⌊counter(0, 1, m)⌋, ⌊counter(1, 1, m)⌋ yield k, i :: earlier(i, xs))))

method main() {
  var i: int;
  var x: int;
  var v: int;
  var largest: int;
  var array: array<int, int>;
  i := 0;
  while i < 100000 {
    v := *;
    array := array[i := v];
    i := i + 1;
  }
  largest := array[0];
  i := 1;
  while i < 100000 {
    if largest < array[i] {
      largest := array[i];
    }
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert largest >= array[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
