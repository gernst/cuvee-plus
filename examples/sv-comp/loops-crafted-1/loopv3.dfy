// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/loopv3.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/loopv3.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of loopv1 with other constants or assertions; checks (j * 4) == i
// note: the concrete loop bounds are symbolic, arbitrary positive values: SIZE for 50000001

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

var SIZE: int;

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  var tmp₁: int;
  SIZE := *;
  assume 0 < SIZE;
  {
    var i: int;
    var j: int;
    i := 0;
    j := 0;
    while i < SIZE {
      tmp₁ := *;
      if (tmp₁ != 0) {
        i := i + 8;
      } else {
        i := i + 4;
      }
    }
    j := (quotient(i, 4));
    assert j * 4 == i;
    result := 0;
    return;
  }
}
