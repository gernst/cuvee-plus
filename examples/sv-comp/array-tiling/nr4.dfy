// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/nr4.dfy
// SV-COMP array-tiling/nr4.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nr2 with other constants or assertions; checks volArray[i] >= MINVAL || volArray[i] == 0

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

var CELLCOUNT: int;

method main() returns (result: int)
  modifies CELLCOUNT
  requires CELLCOUNT == 0
{
  CELLCOUNT := *;
  if CELLCOUNT > 1 {
    var MINVAL: int;
    var i: int;
    var j: int;
    var volArray: array<int, int>;
    MINVAL := 2;
    if (remainder(CELLCOUNT, 4)) != 0 {
      result := 1;
      return;
    }
    assume (remainder(CELLCOUNT, 4)) == 0;
    i := 1;
    while i <= (quotient(CELLCOUNT, 4)) {
      j := 4;
      while j >= 1 {
        if j >= MINVAL {
          volArray := volArray[i * 4 - j := j];
        } else {
          volArray := volArray[i * 4 - j := 0];
        }
        j := j - 1;
      }
      i := i + 1;
    }
    i := 0;
    while i < CELLCOUNT {
      assert volArray[i] >= MINVAL || volArray[i] == 0;
      i := i + 1;
    }
  }
  result := 1;
  return;
}
