// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/for_infinite_loop_1.dfy
// SV-COMP loops/for_infinite_loop_1.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: an infinite loop over i checks x == 0, which stays 0, and the unreachable end checks it
// again
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  var tmp₁: int;
  var i: int, x: int, y: int, n: int;
  i := 0;
  x := 0;
  y := 0;
  tmp₁ := *;
  n := tmp₁;
  if !(n > 0) {
    result := 0;
    return;
  }
  i := 0;
  while ((1) != 0) {
    assert x == 0;
    i := i + 1;
  }
  assert x == 0;
}

// remaining goals of -teq -simplify:
// none
