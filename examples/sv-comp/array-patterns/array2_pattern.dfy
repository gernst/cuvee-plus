// ./Cuvee.sh -teq -simplify examples/sv-comp/array-patterns/array2_pattern.dfy
// SV-COMP array-patterns/array2_pattern.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array10_pattern with other constants or assertions; checks sum == 0

var ARR_SIZE: int;

method main() returns (result: int)
  modifies ARR_SIZE
  requires ARR_SIZE == 0
{
  var tmp₁: int;
  var array1: array<int, int>;
  var array2: array<int, int>;
  var count: int;
  var num: int;
  var index: int;
  var temp: int;
  var sum: int;
  tmp₁ := *;
  ARR_SIZE := tmp₁;
  assume ARR_SIZE > 0;
  count := 0;
  num := -1;
  sum := 0;
  count := 0;
  while count < ARR_SIZE {
    array1 := array1[count := 0];
    array2 := array2[count := 0];
    count := count + 1;
  }
  while (1 != 0) {
    index := *;
    assume index >= 0 && index < ARR_SIZE;
    array1 := array1[index := array1[index] + num * num * index];
    array2 := array2[ARR_SIZE - 1 - index := array2[ARR_SIZE - 1 - index] + num * index];
    temp := *;
    if temp == 0 {
      break;
    }
  }
  count := 0;
  while count < ARR_SIZE {
    sum := sum + array1[count] + array2[count];
    count := count + 1;
  }
  assert sum == 0;
  result := 0;
  return;
}
