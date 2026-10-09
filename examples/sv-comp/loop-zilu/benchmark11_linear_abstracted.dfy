// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark11_linear_abstracted.dfy
// SV-COMP loop-zilu/benchmark11_linear_abstracted.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of benchmark02_linear_abstracted with other constants or assertions;
// checks x==n

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  {
    var x: int;
    var n: int;
    tmp₁ := *;
    x := tmp₁;
    tmp₂ := *;
    n := tmp₂;
    if !(x == 0 && n > 0) {
      result := 0;
      return;
    }
    if x < n {
      x := *;
      if !(x < n) {
        assume false;
      }
      if x < n {
        x := x + 1;
      }
      if x < n {
        assume false;
      }
    }
    assert x == n;
    result := 0;
    return;
  }
}
