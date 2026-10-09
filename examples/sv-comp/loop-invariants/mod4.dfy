// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invariants/mod4.dfy
// SV-COMP ReachSafety-Loops/loop-invariants/mod4.yml (expected: safe), translated from the C program by hand: x
// starts at 0 and is increased by 4 in a nondeterministic loop, and x % 4 == 0 is checked; unsigned int is int, its
// wrap-around at 2^32 keeps the remainder
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var x: int;
  var b: int;
  x := 0;
  havoc b;
  while b != 0 {
    x := x + 4;
    havoc b;
  }
  assert x % 4 == 0;
}

// remaining goals of -teq -simplify:
// none
