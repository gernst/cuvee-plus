// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/trex03-2_abstracted.dfy
// SV-COMP loops/trex03-2_abstracted.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks x1==0 || x2==0 || x3==0

// the bit operations of C on integers, declared only
function bitand(a: int, b: int): int

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var tmp₄: bool;
  var tmp₅: bool;
  var x1: int;
  var x2: int;
  var x3: int;
  var d1: int;
  var d2: int;
  var d3: int;
  var c1: bool;
  var c2: bool;
  tmp₁ := *;
  assume 0 <= tmp₁;
  x1 := tmp₁;
  tmp₂ := *;
  assume 0 <= tmp₂;
  x2 := tmp₂;
  tmp₃ := *;
  assume 0 <= tmp₃;
  x3 := tmp₃;
  d1 := 1;
  d2 := 1;
  d3 := 1;
  tmp₄ := *;
  c1 := tmp₄;
  tmp₅ := *;
  c2 := tmp₅;
  if ((bitand((if x3 > 0 then 1 else 0), bitand((if x2 > 0 then 1 else 0), (if x1 > 0 then 1 else 0)))) != 0) {
    x3 := *;
  assume 0 <= x3;
    x2 := *;
  assume 0 <= x2;
    x1 := *;
  assume 0 <= x1;
    c2 := *;
    c1 := *;
  }
  if ((bitand((if x3 > 0 then 1 else 0), bitand((if x2 > 0 then 1 else 0), (if x1 > 0 then 1 else 0)))) != 0) {
    assume false;
  }
  assert x1 == 0 || x2 == 0 || x3 == 0;
  result := 0;
  return;
}
