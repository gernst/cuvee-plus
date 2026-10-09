// ./Cuvee.sh -teq -simplify examples/sv-comp/array-patterns/array1_pattern_buggy.dfy
// SV-COMP ReachSafety-Arrays/array-patterns/array1_pattern_buggy.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks sum == 0

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
    var temp: int;
    var index: int;
    var sum: int;
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
    while (1 != 0) {
      index := *;
      assume index >= 0 && index < ARR_SIZE;
      if index == 42 {
        array1 := array1[index := 0];
      } else {
        array1 := array1[index := num * (num * index)];
      }
      array2 := array2[ARR_SIZE - 1 - index := num * index];
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
