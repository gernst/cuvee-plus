// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-patterns/array3_pattern_buggy.dfy
// SV-COMP array-patterns/array3_pattern_buggy.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of array1_pattern_buggy with other constants or assertions; checks
// sum1 == sum2

var ARR_SIZE: int;

method square(x: int) returns (result: int) {
  result := x * x;
  return;
}

method main() returns (result: int)
  modifies ARR_SIZE
  requires ARR_SIZE == 0
{
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var array1: array<int, int>;
  var array2: array<int, int>;
  var count: int;
  var num: int;
  var sum1: int;
  var sum2: int;
  var temp: int;
  var index: int;
  tmp₁ := *;
  ARR_SIZE := tmp₁;
  assume ARR_SIZE > 0;
  count := 0;
  num := -1;
  sum1 := 0;
  sum2 := 0;
  count := 0;
  while count < ARR_SIZE {
    array1 := array1[count := 0];
    array2 := array2[count := 0];
    count := count + 1;
  }
  while (1 != 0) {
    index := *;
    assume index >= 0 && index < ARR_SIZE;
    if index == 42 {
      array1 := array1[index := array1[index] + 0];
    } else {
      array1 := array1[index := array1[index] + num * (num * index)];
    }
    array2 := array2[ARR_SIZE - 1 - index := array2[ARR_SIZE - 1 - index] + num * index];
    temp := *;
    if temp == 0 {
      break;
    }
  }
  count := 0;
  while count < ARR_SIZE {
    tmp₂ := square(array1[count]);
    sum1 := sum1 + tmp₂;
    tmp₃ := square(array2[count]);
    sum2 := sum2 + tmp₃;
    count := count + 1;
  }
  assert sum1 == sum2;
  result := 0;
  return;
}
