// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark10_conjunctive.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark10_conjunctive.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: c accumulates i from 0 up to 100, the loop also leaves when i <= 0, and c >= 0 is
// checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int;
  {
    var i: int, c: int;
    tmp₁ := *;
    i := tmp₁;
    tmp₂ := *;
    c := tmp₂;
    if !(c == 0 && i == 0) {
      result := 0;
      return;
    }
    while i < 100 {
      c := c + i;
      i := i + 1;
      if i <= 0 {
        break;
      }
    }
    assert c >= 0;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
