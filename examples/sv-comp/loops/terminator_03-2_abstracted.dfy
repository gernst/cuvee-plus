// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/terminator_03-2_abstracted.dfy
// SV-COMP ReachSafety-Loops/loops/terminator_03-2_abstracted.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of terminator_02-2_abstracted with other constants or assertions; checks y<=0 ||
// (y>0 && x>=100)

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  {
    var x: int;
    var y: int;
    tmp₁ := *;
    x := tmp₁;
    tmp₂ := *;
    y := tmp₂;
    if !(y <= 1000000) {
      result := 0;
      return;
    }
    if y > 0 {
      if x < 100 {
        x := *;
      }
      if x < 100 {
        assume false;
      }
    }
    assert y <= 0 || y > 0 && x >= 100;
    result := 0;
    return;
  }
}
