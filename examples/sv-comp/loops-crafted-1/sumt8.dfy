// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/sumt8.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/sumt8.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of sumt2 with other constants or assertions; checks (i+j+k+v1+v2+v3+v4+v5) == l

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

var SIZE: int;

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  SIZE := 20000001;
  {
    var n: int;
    var i: int;
    var k: int;
    var j: int;
    var l: int;
    var v1: int;
    var v2: int;
    var v3: int;
    var v4: int;
    var v5: int;
    n := 0;
    i := 0;
    k := 0;
    j := 0;
    l := 0;
    v1 := 0;
    v2 := 0;
    v3 := 0;
    v4 := 0;
    v5 := 0;
    n := *;
    if !(n <= SIZE) {
      result := 0;
      return;
    }
    while l < n {
      if !(((remainder(l, 8))) != 0) {
        v5 := v5 + 1;
      } else if !(((remainder(l, 7))) != 0) {
        v1 := v1 + 1;
      } else if !(((remainder(l, 6))) != 0) {
        v2 := v2 + 1;
      } else if !(((remainder(l, 5))) != 0) {
        v3 := v3 + 1;
      } else if !(((remainder(l, 4))) != 0) {
        v4 := v4 + 1;
      } else if !(((remainder(l, 3))) != 0) {
        i := i + 1;
      } else if !(((remainder(l, 2))) != 0) {
        j := j + 1;
      } else {
        k := k + 1;
      }
      l := l + 1;
      assert i + j + k + v1 + v2 + v3 + v4 + v5 == l;
    }
    result := 0;
    return;
  }
}
