// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark37_conjunctive.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark37_conjunctive.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: x and y count down together while x > 0, and y >= 0 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int;
  {
    var x: int, y: int;
    tmp₁ := *;
    x := tmp₁;
    tmp₂ := *;
    y := tmp₂;
    if !(x == y && x >= 0) {
      result := 0;
      return;
    }
    while x > 0 {
      x := x - 1;
      y := y - 1;
    }
    assert y >= 0;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
