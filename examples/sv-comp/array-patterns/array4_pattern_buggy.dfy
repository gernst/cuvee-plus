// ./Cuvee.sh -teq -simplify examples/sv-comp/array-patterns/array4_pattern_buggy.dfy
// SV-COMP array-patterns/array4_pattern_buggy.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of array1_pattern_buggy with other constants or assertions; checks
// sum == 0

var ARR_SIZE: int;

method main() returns (result: int)
  modifies ARR_SIZE
  requires ARR_SIZE == 0
{
  {
    var array1: array<int, int>;
    var array2: array<int, int>;
    var count: int;
    var num: int;
    var sum: int;
    var temp: int;
    var index1: int;
    var index2: int;
    ARR_SIZE := *;
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
      index1 := *;
      index2 := *;
      assume index1 >= 0 && index1 < ARR_SIZE;
      assume index2 >= 0 && index2 < ARR_SIZE;
      assume array1[index1] == 0;
      assume array2[index2] == 0;
      if index1 == 42 {
        array1 := array1[index1 := 0];
      } else {
        array1 := array1[index1 := num * (num * count)];
      }
      array2 := array2[index2 := num * count];
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
}
