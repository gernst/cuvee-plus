// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-patterns/array5_pattern.dfy
// SV-COMP array-patterns/array5_pattern.yml (expected: safe), translated from the C program by
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
  var sum: int;
  var temp: int;
  var index: int;
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
  count := 1;
  while (1 != 0) {
    index := *;
    assume index >= 0 && index < ARR_SIZE;
    if (rem(index, 2)) == 0 {
      array1 := array1[index := num * (num * count)];
      array2 := array2[index := num * count];
    } else {
      array1 := array1[index := num * count];
      array2 := array2[index := num * (num * count)];
    }
    if count == 200 {
      count := 0;
    }
    count := count + 1;
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
