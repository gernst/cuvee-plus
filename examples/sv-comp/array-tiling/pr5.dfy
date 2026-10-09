// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/pr5.dfy
// SV-COMP array-tiling/pr5.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of pr2 with other constants or assertions; checks volArray[i] >= MINVAL || volArray[i] == 0

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
  var CCCELVOL5: int;
  var CCCELVOL4: int;
  var CCCELVOL3: int;
  var CCCELVOL2: int;
  var CCCELVOL1: int;
  CELLCOUNT := *;
  if CELLCOUNT > 1 {
    CCCELVOL5 := 2;
    CCCELVOL4 := 5;
    CCCELVOL3 := 7;
    CCCELVOL2 := 3;
    CCCELVOL1 := 1;
    if (remainder(CELLCOUNT, 5)) != 0 {
      result := 1;
      return;
    }
    assume (remainder(CELLCOUNT, 5)) == 0;
    i := 1;
    while i <= (quotient(CELLCOUNT, 5)) {
      if CCCELVOL5 >= MINVAL {
        volArray := volArray[i * 5 - 5 := CCCELVOL5];
      } else {
        volArray := volArray[i * 5 - 5 := 0];
      }
      if CCCELVOL4 >= MINVAL {
        volArray := volArray[i * 5 - 4 := CCCELVOL4];
      } else {
        volArray := volArray[i * 5 - 4 := 0];
      }
      if CCCELVOL3 >= MINVAL {
        volArray := volArray[i * 5 - 3 := CCCELVOL3];
      } else {
        volArray := volArray[i * 5 - 3 := 0];
      }
      if CCCELVOL2 >= MINVAL {
        volArray := volArray[i * 5 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 5 - 2 := 0];
      }
      if CCCELVOL1 >= MINVAL {
        volArray := volArray[i * 5 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 5 - 1 := 0];
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
