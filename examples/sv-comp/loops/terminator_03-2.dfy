// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/terminator_03-2.dfy
// SV-COMP ReachSafety-Loops/loops/terminator_03-2.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: x grows by y > 0 until it reaches 100, which is checked
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
    if !(y <= 1000000) {
      result := 0;
      return;
    }
    if y > 0 {
      while x < 100 {
        x := x + y;
      }
    }
    assert y <= 0 || y > 0 && x >= 100;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
