// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_maxInArray_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_maxInArray_ground.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy and by hand: the array is filled with arbitrary values, its maximum is computed
// (starting from 0), and each element is checked to be at most the maximum
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the filling loop is introduced
// as stores(a, ⌊J⌋, Tmp), whose reads at i < n are earlier(i, Tmp), the loop of the maximum as maxs(0, maps(...
// a[i] ...)), and the assertion a[x] <= max follows from earlier(k, values) <= current(maxs(x, values))

method main() {
  var a: array<int, int>;
  var max: int;
  var i: int;
  var x: int;
  var j: int;
  var tmp: int;
  max := 0;
  j := 0;
  while j < 100000 {
    tmp := *;
    a := a[j := tmp];
    j := j + 1;
  }
  i := 0;
  while i < 100000 {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a[x] <= max;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
