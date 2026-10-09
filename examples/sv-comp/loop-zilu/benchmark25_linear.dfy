// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark25_linear.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark25_linear.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x counts up to 10, and x == 10 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (the _abstracted variant is the
// same program with an abstracted loop)

method main() returns (result: int) {
  var tmp₁: int;
  {
    var x: int;
    havoc tmp₁;
    x := tmp₁;
    if !(x < 0) {
      result := 0;
      return;
    }
    while x < 10 {
      x := x + 1;
    }
    assert x == 10;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
