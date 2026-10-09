// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/terminator_02-2_abstracted.dfy
// SV-COMP loops/terminator_02-2_abstracted.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of terminator_03-2_abstracted with other constants or assertions; checks x>=100
// || z<=100

// the bit operations of C on integers, declared only
function bitand(a: int, b: int): int

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  {
    var x: int;
    var z: int;
    tmp₁ := *;
    x := tmp₁;
    tmp₂ := *;
    z := tmp₂;
    if !(x > -100) {
      result := 0;
      return;
    }
    if !(x < 200) {
      result := 0;
      return;
    }
    if !(z > 100) {
      result := 0;
      return;
    }
    if !(z < 200) {
      result := 0;
      return;
    }
    if ((bitand((if z > 100 then 1 else 0), (if x < 100 then 1 else 0))) != 0) {
      z := *;
      x := *;
    }
    if ((bitand((if z > 100 then 1 else 0), (if x < 100 then 1 else 0))) != 0) {
      assume false;
    }
    assert x >= 100 || z <= 100;
    result := 0;
    return;
  }
}
