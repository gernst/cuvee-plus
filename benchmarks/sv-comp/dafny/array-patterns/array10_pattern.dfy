// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-patterns/array10_pattern.dfy
// SV-COMP array-patterns/array10_pattern.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array1_pattern with other constants or assertions; checks 4 * sum <=
// (ARR_SIZE-1)*(ARR_SIZE+1)

var ARR_SIZE: int;

method main() returns (result: int)
  modifies ARR_SIZE
  requires ARR_SIZE == 0
{
  var tmp₁: int;
  var tmp₂: int;
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
  while (1 != 0) {
    tmp₂ := *;
    index := tmp₂;
    assume index >= 0 && index < ARR_SIZE;
    array1 := array1[index := num * (num * (num * (num * index)))];
    array2 := array2[index := if (rem(index, 2)) != 0 then num * index else array2[index]];
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
  assert 4 * sum <= (ARR_SIZE - 1) * (ARR_SIZE + 1);
  result := 0;
  return;
}
