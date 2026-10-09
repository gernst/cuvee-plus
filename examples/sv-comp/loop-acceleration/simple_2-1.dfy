// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/simple_2-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/simple_2-1.yml (expected: safe), translated from the C program by
// hand: an arbitrary x >= 0 (unsigned) is increased while below 0x0fffffff, and checked to be at least that
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var x: int;
  havoc x;
  assume x >= 0;
  while x < 268435455 {
    x := x + 1;
  }
  assert x >= 268435455;
}

// remaining goals of -teq -simplify:
// none
