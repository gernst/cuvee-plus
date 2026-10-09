// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/sum_by_3_abstracted.dfy
// SV-COMP loops-crafted-1/sum_by_3_abstracted.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a program of the folder; checks (i+j+k)/3 <= SIZE

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

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
    n := *;
    assume 0 <= n;
    if !(n <= SIZE) {
      result := 0;
      return;
    }
    i := 0;
    if i < n {
      i := *;
    assume 0 <= i;
      if !(i < n) {
        assume false;
      }
      if i < n {
        i := i + 1;
      }
      if i < n {
        assume false;
      }
    }
    j := i;
    while j < n {
      j := j + 1;
    }
    k := j;
    while k < n {
      k := k + 1;
    }
    assert (quotient(i + j + k, 3)) <= SIZE;
    result := 0;
    return;
  }
}
