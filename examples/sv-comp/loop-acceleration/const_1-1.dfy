// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/const_1-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/const_1-1.yml (expected: safe), translated from the C program by
// hand: x is set to 0 in each of 1024 iterations, and is 0 then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var x: int;
  var y: int;
  x := 1;
  y := 0;
  while y < 1024 {
    x := 0;
    y := y + 1;
  }
  assert x == 0;
}

// remaining goals of -teq -simplify:
// none
