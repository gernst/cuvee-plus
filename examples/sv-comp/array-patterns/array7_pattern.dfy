// ./Cuvee.sh -teq -simplify examples/sv-comp/array-patterns/array7_pattern.dfy
// SV-COMP array-patterns/array7_pattern.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array10_pattern with other constants or assertions; checks sum == 0

var ARR_SIZE: int;

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
  var sum: int;
  var temp: int;
  var index: int;
  var pivot: int;
  tmp₁ := *;
  ARR_SIZE := tmp₁;
  assume ARR_SIZE > 0;
  count := 0;
  num := -1;
  sum := 0;
  count := 0;
  while count < ARR_SIZE {
    array1 := array1[count := num * (num * count)];
    array2 := array2[count := num * count];
    count := count + 1;
  }
  while (1 != 0) {
    tmp₂ := *;
    index := tmp₂;
    tmp₃ := *;
    pivot := tmp₃;
    assume pivot > 0;
    assume index >= pivot && index < ARR_SIZE - pivot;
    array1 := array1[index := array1[index - pivot] + array1[index + pivot]];
    array2 := array2[index := array2[index - pivot] + array2[index + pivot]];
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
