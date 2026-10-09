// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/simple_1-2.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/simple_1-2.yml (expected: safe), translated from the C program by
// hand: x is increased by 2 from 0 while below 0x0fffffff, and checked to be even (no wrap-around below the bound)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (simple_1-1 and the other -1
// variants are unsafe, the _abstracted variants are the same programs with abstracted loops)

method main() {
  var x: int;
  x := 0;
  while x < 268435455 {
    x := x + 2;
  }
  assert x % 2 == 0;
}

// remaining goals of -teq -simplify:
// none
