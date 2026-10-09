// ./Cuvee.sh -teq -simplify examples/sv-comp/array-patterns/array26_pattern.dfy
// SV-COMP array-patterns/array26_pattern.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array10_pattern with other constants or assertions; checks sum == 0 || sum ==
// 1

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

var ARR_SIZE: int;

method main() returns (result: int)
  modifies ARR_SIZE
  requires ARR_SIZE == 0
{
  var tmp₁: int;
  {
    var array: array<int, array<int, int>>;
    var row: int;
    var column: int;
    var num: int;
    var value: int;
    var sum: int;
    tmp₁ := *;
    ARR_SIZE := tmp₁;
    assume ARR_SIZE > 1;
    row := 0;
    column := 0;
    num := -1;
    value := 1;
    sum := 0;
    row := 0;
    while row < ARR_SIZE {
      column := 0;
      while column < ARR_SIZE {
        if (remainder(row, 2)) == 0 && (remainder(column, 2)) == 0 {
          array := array[row := array[row][column := value]];
          value := value * num;
        } else if (remainder(row, 2)) == 1 && (remainder(column, 2)) == 1 {
          array := array[row := array[row][column := value]];
          value := value * num;
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
    assert sum == 0 || sum == 1;
    result := 0;
    return;
  }
}
