// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/simple_4-2.dfy
// SV-COMP loop-acceleration/simple_4-2.yml (expected: safe), translated from the C program by
// hand: x counts down by 2 from 268435440 (0x0ffffff0), an even number, to 0, and is even then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var x: int;
  x := 268435440;
  while x > 0 {
    x := x - 2;
  }
  assert rem(x, 2) == 0;
}

// remaining goals of -teq -simplify:
// none
