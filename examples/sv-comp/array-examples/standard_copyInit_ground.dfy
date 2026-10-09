// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copyInit_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_copyInit_ground.yml (expected: safe), translated from the C program by hand:
// a is set to 42, copied into b, and b is checked to be 42
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var x: int;
  var a: array<int, int>;
  var b: array<int, int>;
  i := 0;
  while i < 100000 {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    b := b[i := a[i]];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert b[x] == 42;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
