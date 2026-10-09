// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copyInitSum2_ground-2.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_copyInitSum2_ground-2.yml (expected: safe), translated from
// the C program by hand: a is initialized to 42, copied into b, and the index is added to each element of b, which
// is then 42 + x
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the update b[i] + i reads the
// stores of the copy at the same position
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var x: int;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := b[i] + i];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert b[x] == 42 + x;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
