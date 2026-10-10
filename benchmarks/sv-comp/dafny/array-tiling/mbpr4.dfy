// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-tiling/mbpr4.dfy
// SV-COMP array-tiling/mbpr4.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of mbpr2 with other constants or assertions; checks volArray[i] >= MINVAL || volArray[i] ==
// 0

var CELLCOUNT: int;

method main() returns (result: int)
  modifies CELLCOUNT
  requires CELLCOUNT == 0
{
  var MINVAL: int;
  var i: int;
  var volArray: array<int, int>;
  var CCCELVOL4: int;
  var CCCELVOL3: int;
  var CCCELVOL2: int;
  var CCCELVOL1: int;
  CELLCOUNT := *;
  if CELLCOUNT > 1 {
    MINVAL := 2;
    CCCELVOL4 := 5;
    CCCELVOL3 := 7;
    CCCELVOL2 := 3;
    CCCELVOL1 := 1;
    if (rem(CELLCOUNT, 4)) != 0 {
      result := 1;
      return;
    }
    assume (rem(CELLCOUNT, 4)) == 0;
    i := 1;
    while i <= (quot(CELLCOUNT, 4)) {
      if CCCELVOL4 >= MINVAL {
        volArray := volArray[i * 4 - 4 := CCCELVOL4];
      } else {
        volArray := volArray[i * 4 - 4 := 0];
      }
      volArray := volArray[i * 4 - 3 := volArray[i * 4 - 3]];
      volArray := volArray[i * 4 - 2 := volArray[i * 4 - 2]];
      volArray := volArray[i * 4 - 1 := volArray[i * 4 - 1]];
      i := i + 1;
    }
    i := 1;
    while i <= (quot(CELLCOUNT, 4)) {
      if CCCELVOL3 >= MINVAL {
        volArray := volArray[i * 4 - 3 := CCCELVOL3];
      } else {
        volArray := volArray[i * 4 - 3 := 0];
      }
      volArray := volArray[i * 4 - 4 := volArray[i * 4 - 4]];
      volArray := volArray[i * 4 - 2 := volArray[i * 4 - 2]];
      volArray := volArray[i * 4 - 1 := volArray[i * 4 - 1]];
      i := i + 1;
    }
    i := 1;
    while i <= (quot(CELLCOUNT, 4)) {
      if CCCELVOL2 >= MINVAL {
        volArray := volArray[i * 4 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 4 - 2 := 0];
      }
      volArray := volArray[i * 4 - 4 := volArray[i * 4 - 4]];
      volArray := volArray[i * 4 - 3 := volArray[i * 4 - 3]];
      volArray := volArray[i * 4 - 1 := volArray[i * 4 - 1]];
      i := i + 1;
    }
    i := 1;
    while i <= (quot(CELLCOUNT, 4)) {
      if CCCELVOL1 >= MINVAL {
        volArray := volArray[i * 4 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 4 - 1 := 0];
      }
      volArray := volArray[i * 4 - 4 := volArray[i * 4 - 4]];
      volArray := volArray[i * 4 - 3 := volArray[i * 4 - 3]];
      volArray := volArray[i * 4 - 2 := volArray[i * 4 - 2]];
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
