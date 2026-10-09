// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark35_linear.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark35_linear.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x counts up to 10 from a nonnegative value, and x >= 10 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  var tmp₁: int;
  {
    var x: int;
    havoc tmp₁;
    x := tmp₁;
    if !(x >= 0) {
      result := 0;
      return;
    }
    while x >= 0 && x < 10 {
      x := x + 1;
    }
    assert x >= 10;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
