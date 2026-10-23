// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-invariants/odd.dfy
// SV-COMP loop-invariants/odd.yml (expected: safe), translated from the C program by hand: x
// starts at 1 and is increased by 2 in a nondeterministic loop, and x % 2 == 1 is checked; unsigned int is int, its
// wrap-around at 2^32 keeps the remainder
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var x: int;
  var b: int;
  x := 1;
  b := *;
  while b != 0 {
    x := x + 2;
    b := *;
  }
  assert rem(x, 2) == 1;
}

// remaining goals of -teq -simplify:
// none
