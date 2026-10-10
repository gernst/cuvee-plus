// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-tiling/nr5.dfy
// SV-COMP array-tiling/nr5.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nr2 with other constants or assertions; checks volArray[i] >= MINVAL || volArray[i] == 0

var CELLCOUNT: int;

method main() returns (result: int)
  modifies CELLCOUNT
  requires CELLCOUNT == 0
{
  var DEFAULTVALUE: int;
  var MINVAL: int;
  var i: int;
  var j: int;
  var volArray: array<int, int>;
  CELLCOUNT := *;
  if CELLCOUNT > 1 {
    DEFAULTVALUE := 1;
    MINVAL := 2;
    if (rem(CELLCOUNT, 5)) != 0 {
      result := 1;
      return;
    }
    assume (rem(CELLCOUNT, 5)) == 0;
    i := 1;
    while i <= (quot(CELLCOUNT, 5)) {
      j := 5;
      while j >= 1 {
        if j >= MINVAL {
          volArray := volArray[i * 5 - j := j];
        } else {
          volArray := volArray[i * 5 - j := 0];
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
