// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-tiling/rewnifrev.dfy
// SV-COMP array-tiling/rewnifrev.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks a[i] >= i

var SIZE: int;

var MAX: int;

method main() returns (result: int)
  modifies MAX, SIZE
  requires SIZE == 0 && MAX == 0
{
  var i: int;
  var a: array<int, int>;
  MAX := 100000;
  SIZE := *;
  if SIZE > 1 && SIZE < MAX {
    i := SIZE - 1;
    while i >= 0 {
      if i - 1 >= 0 {
        a := a[i - 1 := i - 2];
      }
      a := a[i := i];
      i := i - 1;
    }
    i := 0;
    while i < SIZE {
      assert a[i] >= i;
      i := i + 1;
    }
  }
  result := 1;
  return;
}
