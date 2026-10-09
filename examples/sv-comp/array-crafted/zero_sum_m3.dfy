// ./Cuvee.sh -teq -simplify examples/sv-comp/array-crafted/zero_sum_m3.dfy
// SV-COMP array-crafted/zero_sum_m3.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of zero_sum_m2 with other constants or assertions; checks sum == 0

var SIZE: int;

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  var tmp₂: int;
  var i: int;
  var a: array<int, int>;
  var sum: int;
  var i₁: int;
  SIZE := *;
  if SIZE > 1 {
    sum := 0;
    i₁ := 0;
    while i₁ < SIZE {
      tmp₂ := *;
      a := a[i₁ := tmp₂];
      i₁ := i₁ + 1;
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
