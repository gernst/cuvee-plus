// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/mine2017-ex4.10.dfy
// SV-COMP ReachSafety-Loops/loop-lit/mine2017-ex4.10.yml (expected: safe), translated from the C program by hand: v
// counts up by 2 from 1 while v <= 50, and ends at 51 or 52
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var v: int;
  v := 1;
  while v <= 50 {
    assert 1 <= v;
    v := v + 2;
    assert v <= 52;
  }
  assert 51 <= v;
  assert v <= 52;
}

// remaining goals of -teq -simplify:
// none
