// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/underapprox_2-2.dfy
// SV-COMP loop-acceleration/underapprox_2-2.yml (expected: safe), translated from the C program
// by hand: as underapprox_1-2, with the assertion on x, which counts to 6
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the assertion is on the counter
// x, not on the geometric y

method main() {
  var x: int;
  var y: int;
  x := 0;
  y := 1;
  while x < 6 {
    x := x + 1;
    y := y * 2;
  }
  assert x == 6;
}

// remaining goals of -teq -simplify:
// none
