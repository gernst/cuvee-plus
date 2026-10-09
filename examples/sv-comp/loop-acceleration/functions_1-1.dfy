// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/functions_1-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/functions_1-1.yml (expected: safe), translated from the C program by
// hand: x is updated by f(x) = x + 2 up to 268435455 (0x0fffffff), and is even then
//
// findings: with the definition of f as a rewrite rule, the update is x + 2, which teq.dfy accelerates to
// counter(0, 2, n); closed (no output); without {:rw}, f is not unfolded and the goal remains

// f is a rewrite rule, i.e., it is unfolded, as the C function is inlined by verification tools
function {:rw} f(z: int): int {
  z + 2
}

method main() {
  var x: int;
  x := 0;
  while x < 268435455 {
    x := f(x);
  }
  assert x % 2 == 0;
}

// remaining goals of -teq -simplify:
// none
