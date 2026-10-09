// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_init5_ground-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_init5_ground-1.yml (expected: safe), translated from the C program by hand:
// the array is set to 42, 43, 44, 45, 46 by five loops, and checked to be 46
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output), in about the time of the copies
// (see the summary, performance)

method main() {
  var i: int;
  var x: int;
  var a: array<int, int>;
  i := 0;
  while i < 100000 {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a := a[i := 43];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a := a[i := 44];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a := a[i := 45];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a := a[i := 46];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a[x] == 46;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
