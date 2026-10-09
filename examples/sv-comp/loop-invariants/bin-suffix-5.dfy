// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invariants/bin-suffix-5.dfy
// SV-COMP ReachSafety-Loops/loop-invariants/bin-suffix-5.yml (expected: safe), translated from the C program by
// hand: x starts at 5 and is increased by 8 in a nondeterministic loop, (x & 5) == 5 is checked, here as x % 8 ==
// 5, which implies it (the Dafny frontend has no bitwise operators); unsigned int is int, its wrap-around at 2^32,
// a multiple of 8, keeps the remainder
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output), with the assertion as x % 8 == 5

method main() {
  var x: int;
  var b: int;
  x := 5;
  b := *;
  while b != 0 {
    x := x + 8;
    b := *;
  }
  assert x % 8 == 5;
}

// remaining goals of -teq -simplify:
// none
