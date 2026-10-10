// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/for_infinite_loop_2.dfy
// SV-COMP loops/for_infinite_loop_2.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: as for_infinite_loop_1, with the unreachable end checking x != 0
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the end after the infinite loop
// is unreachable

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
  assert x != 0;
}

// remaining goals of -teq -simplify:
// none
