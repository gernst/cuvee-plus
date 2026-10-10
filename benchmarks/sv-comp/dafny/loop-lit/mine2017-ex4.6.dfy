// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-lit/mine2017-ex4.6.dfy
// SV-COMP loop-lit/mine2017-ex4.6.yml (expected: safe), translated from the C program by hand: x
// counts down from 40 to 0, with the bounds checked in the loop
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var x: int;
  x := 40;
  while x != 0 {
    assert x <= 40;
    x := x - 1;
    assert x >= 0;
  }
  assert x == 0;
}

// remaining goals of -teq -simplify:
// none
