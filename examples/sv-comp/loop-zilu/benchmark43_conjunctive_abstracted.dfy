// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark43_conjunctive_abstracted.dfy
// SV-COMP loop-zilu/benchmark43_conjunctive_abstracted.yml (expected: safe), translated from the
// C program by ./Cuvee.sh -print dfy: a program of the folder; checks x == 100 || y == 100

// the bit operations of C on integers, declared only
function bitand(a: int, b: int): int

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var x: int;
  var y: int;
  tmp₁ := *;
  x := tmp₁;
  tmp₂ := *;
  y := tmp₂;
  if !(x < 100 && y < 100) {
    result := 0;
    return;
  }
  if ((bitand((if y < 100 then 1 else 0), (if x < 100 then 1 else 0))) != 0) {
    x := *;
    y := *;
    if !((bitand((if y < 100 then 1 else 0), (if x < 100 then 1 else 0))) != 0) {
      assume false;
    }
    if x < 100 && y < 100 {
      x := x + 1;
      y := y + 1;
    }
    if ((bitand((if y < 100 then 1 else 0), (if x < 100 then 1 else 0))) != 0) {
      assume false;
    }
  }
  assert x == 100 || y == 100;
  result := 0;
  return;
}
