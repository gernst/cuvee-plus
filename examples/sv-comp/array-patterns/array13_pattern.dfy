// ./Cuvee.sh -teq -simplify examples/sv-comp/array-patterns/array13_pattern.dfy
// SV-COMP array-patterns/array13_pattern.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array10_pattern with other constants or assertions; checks 2*sum <=
// ARR_SIZE*(ARR_SIZE-1)

var ARR_SIZE: int;

method main() returns (result: int)
  modifies ARR_SIZE
  requires ARR_SIZE == 0
{
  var tmp₁: int;
  var array: array<int, array<int, int>>;
  var row: int;
  var column: int;
  var num: int;
  var sum: int;
  var temp: int;
  var index1: int;
  var index2: int;
  tmp₁ := *;
  ARR_SIZE := tmp₁;
  assume ARR_SIZE > 0;
  row := 0;
  column := 0;
  num := -1;
  sum := 0;
  row := 0;
  while row < ARR_SIZE {
    column := 0;
    while column < ARR_SIZE {
      array := array[row := array[row][column := 0]];
      column := column + 1;
    }
    row := row + 1;
  }
  while (1 != 0) {
    index1 := *;
    index2 := *;
    assume index1 >= 0 && index1 < ARR_SIZE;
    assume index2 >= 0 && index2 < ARR_SIZE;
    array := array[index1 := array[index1][index2 := if index1 > index2
          then num * num * num * num
          else array[index1][index2]]];
    temp := *;
    if temp == 0 {
      break;
    }
  }
  row := 0;
  while row < ARR_SIZE {
    column := 0;
    while column < ARR_SIZE {
      sum := sum + array[row][column];
      column := column + 1;
    }
    row := row + 1;
  }
  assert 2 * sum <= ARR_SIZE * (ARR_SIZE - 1);
  result := 0;
  return;
}
