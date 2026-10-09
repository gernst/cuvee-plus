// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark26_linear_abstracted.dfy
// SV-COMP loop-zilu/benchmark26_linear_abstracted.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of benchmark02_linear_abstracted with other constants or assertions;
// checks x==y

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
    if !(x < y) {
      result := 0;
      return;
    }
    if x < y {
      x := *;
      if !(x < y) {
        assume false;
      }
      if x < y {
        x := x + 1;
      }
      if x < y {
        assume false;
      }
    }
    assert x == y;
    result := 0;
    return;
  }
}
