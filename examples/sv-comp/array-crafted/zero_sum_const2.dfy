// ./Cuvee.sh -teq -simplify examples/sv-comp/array-crafted/zero_sum_const2.dfy
// SV-COMP ReachSafety-Arrays/array-crafted/zero_sum_const2.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of zero_sum_const1 with other constants or assertions; checks sum == 0

var SIZE: int;

var MAX: int;

method main() returns (result: int)
  modifies MAX, SIZE
  requires SIZE == 0 && MAX == 0
{
  MAX := 100000;
  SIZE := *;
  if SIZE > 1 && SIZE < MAX {
    var i: int;
    var a: array<int, int>;
    var sum: int;
    sum := 0;
    i := 0;
    while i < SIZE {
      a := a[i := 1];
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      sum := sum - a[i];
      i := i + 1;
    }
    assert sum == 0;
  }
  result := 1;
  return;
}
