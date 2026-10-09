// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/ddlm2013.dfy
// SV-COMP loop-lit/ddlm2013.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks a == b

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  {
    var i: int;
    var j: int;
    var a: int;
    var b: int;
    var flag: int;
    tmp₁ := *;
    flag := tmp₁;
    a := 0;
    b := 0;
    j := 1;
    if (flag != 0) {
      i := 0;
    } else {
      i := 1;
    }
    while true {
      tmp₂ := *;
      if !(tmp₂ != 0) {
        break;
      }
      a := a + 1;
      b := b + (j - i);
      i := i + 2;
      if (remainder(i, 2)) == 0 {
        j := j + 2;
      } else {
        j := j + 1;
      }
    }
    if (flag != 0) {
      assert a == b;
    }
    result := 0;
    return;
  }
}
