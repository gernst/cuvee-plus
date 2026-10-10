// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-crafted/zero_sum_const_m3.dfy
// SV-COMP array-crafted/zero_sum_const_m3.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of zero_sum_const_m2 with other constants or assertions; checks sum == 0

var SIZE: int;

var MAX: int;

method main() returns (result: int)
  modifies MAX, SIZE
  requires SIZE == 0 && MAX == 0
{
  var i: int;
  var a: array<int, int>;
  var sum: int;
  MAX := 100000;
  SIZE := *;
  if SIZE > 1 && SIZE < MAX {
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
      sum := sum + a[i];
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
      sum := sum - a[i];
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
