// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_minInArray_ground-2.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_minInArray_ground-2.yml (expected: safe), translated from the
// C program by hand: the array is filled with arbitrary values, its minimum is computed (starting from 0), and each
// element is at least the minimum
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the minimum is mins, dual to
// standard_maxInArray_ground

method main() {
  var a: array<int, int>;
  var min: int;
  var i: int;
  var x: int;
  var tmp: int;
  min := 0;
  i := 0;
  while i < 100000 {
    tmp := *;
    a := a[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a[x] >= min;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
