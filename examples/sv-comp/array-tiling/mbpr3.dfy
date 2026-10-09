// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/mbpr3.dfy
// SV-COMP array-tiling/mbpr3.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of mbpr2 with other constants or assertions; checks volArray[i] >= MINVAL || volArray[i] ==
// 0

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

var CELLCOUNT: int;

method main() returns (result: int)
  modifies CELLCOUNT
  requires CELLCOUNT == 0
{
  var MINVAL: int;
  var i: int;
  var volArray: array<int, int>;
  var CCCELVOL3: int;
  var CCCELVOL2: int;
  var CCCELVOL1: int;
  CELLCOUNT := *;
  if CELLCOUNT > 1 {
    MINVAL := 2;
    CCCELVOL3 := 7;
    CCCELVOL2 := 3;
    CCCELVOL1 := 1;
    if (remainder(CELLCOUNT, 3)) != 0 {
      result := 1;
      return;
    }
    assume (remainder(CELLCOUNT, 3)) == 0;
    i := 1;
    while i <= (quotient(CELLCOUNT, 3)) {
      if CCCELVOL3 >= MINVAL {
        volArray := volArray[i * 3 - 3 := CCCELVOL3];
      } else {
        volArray := volArray[i * 3 - 3 := 0];
      }
      volArray := volArray[i * 3 - 2 := volArray[i * 3 - 2]];
      volArray := volArray[i * 3 - 1 := volArray[i * 3 - 1]];
      i := i + 1;
    }
    i := 1;
    while i <= (quotient(CELLCOUNT, 3)) {
      if CCCELVOL2 >= MINVAL {
        volArray := volArray[i * 3 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 3 - 2 := 0];
      }
      volArray := volArray[i * 3 - 3 := volArray[i * 3 - 3]];
      volArray := volArray[i * 3 - 1 := volArray[i * 3 - 1]];
      i := i + 1;
    }
    i := 1;
    while i <= (quotient(CELLCOUNT, 3)) {
      if CCCELVOL1 >= MINVAL {
        volArray := volArray[i * 3 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 3 - 1 := 0];
      }
      volArray := volArray[i * 3 - 2 := volArray[i * 3 - 2]];
      volArray := volArray[i * 3 - 3 := volArray[i * 3 - 3]];
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
