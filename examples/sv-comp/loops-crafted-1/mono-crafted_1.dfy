// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_1.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/mono-crafted_1.yml (expected: safe), translated from the C program by
// hand: x counts to 1000000 and y, from 50000, counts along from x == 50000 on, then both count down until y is z,
// i.e., 0, when x is 0 as well
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the two-phase loop of gj2007 and
// a loop that counts both down

method main() {
  var x: int;
  var y: int;
  var z: int;
  x := 0;
  y := 50000;
  z := 0;
  x := 0;
  while x < 1000000 {
    if x < 50000 {
      x := x + 1;
    } else {
      x := x + 1;
      y := y + 1;
    }
  }
  while y > z {
    y := y - 1;
    x := x - 1;
  }
  assert x == z;
}

// remaining goals of -teq -simplify:
// none
