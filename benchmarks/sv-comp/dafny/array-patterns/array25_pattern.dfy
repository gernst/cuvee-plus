// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-patterns/array25_pattern.dfy
// SV-COMP array-patterns/array25_pattern.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array10_pattern with other constants or assertions; checks sum == 0 || sum ==
// ARR_SIZE

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
  tmp₁ := *;
  ARR_SIZE := tmp₁;
  assume ARR_SIZE > 1;
  row := 0;
  column := 0;
  num := -1;
  sum := 0;
  row := 0;
  while row < ARR_SIZE {
    column := 0;
    while column < ARR_SIZE {
      if (rem(row, 2)) == 0 && (rem(column, 2)) == 0 {
        array := array[row := array[row][column := num * num]];
      } else if (rem(row, 2)) == 1 && (rem(column, 2)) == 1 {
        array := array[row := array[row][column := num]];
      } else {
        array := array[row := array[row][column := 0]];
      }
      column := column + 1;
    }
    row := row + 1;
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
  assert sum == 0 || sum == ARR_SIZE;
  result := 0;
  return;
}
