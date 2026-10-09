// ./Cuvee.sh -teq -simplify examples/sv-comp/array-patterns/array11_pattern.dfy
// SV-COMP ReachSafety-Arrays/array-patterns/array11_pattern.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array10_pattern with other constants or assertions; checks sum == 0 || (sum+2
// == 2 * ARR_SIZE)

var ARR_SIZE: int;

method main() returns (result: int)
  modifies ARR_SIZE
  requires ARR_SIZE == 0
{
  var tmp₁: int;
  var tmp₂: int;
  {
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
      array2 := array2[index := if index == ARR_SIZE - 1 then index else num * index];
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
    assert sum == 0 || sum + 2 == 2 * ARR_SIZE;
    result := 0;
    return;
  }
}
