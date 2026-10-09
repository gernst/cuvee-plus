// ./Cuvee.sh -teq -simplify examples/sv-comp/array-patterns/array27_pattern.dfy
// SV-COMP array-patterns/array27_pattern.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array10_pattern with other constants or assertions; checks 2*sum ==
// (ARR_SIZE*(ARR_SIZE-1)*(ARR_SIZE-1))

var ARR_SIZE: int;

method main() returns (result: int)
  modifies ARR_SIZE
  requires ARR_SIZE == 0
{
  var tmp₁: int;
  var array: array<int, array<int, int>>;
  var row: int;
  var column: int;
  var sum: int;
  tmp₁ := *;
  ARR_SIZE := tmp₁;
  assume ARR_SIZE > 0;
  row := 0;
  column := 0;
  sum := 0;
  row := 0;
  while row < ARR_SIZE {
    column := 0;
    while column < ARR_SIZE {
      if row == column {
        array := array[row := array[row][row := 0]];
      } else {
        array := array[row := array[row][column := row]];
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
  assert 2 * sum == ARR_SIZE * (ARR_SIZE - 1) * (ARR_SIZE - 1);
  result := 0;
  return;
}
