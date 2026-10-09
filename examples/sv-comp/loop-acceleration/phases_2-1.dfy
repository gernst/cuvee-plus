// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/phases_2-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/phases_2-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of phases_1-1 with other constants or assertions; checks x != y

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

method main() returns (result: int) {
  var tmp₁: int;
  {
    var x: int;
    var y: int;
    x := 1;
    tmp₁ := *;
    assume 0 <= tmp₁;
    y := tmp₁;
    if !(y > 0) {
      result := 0;
      return;
    }
    while x < y {
      if x < (quotient(y, x)) {
        x := x * x;
      } else {
        x := x + 1;
      }
    }
    assert x != y;
  }
}
