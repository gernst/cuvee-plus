// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-tiling/rewnifrev2.dfy
// SV-COMP array-tiling/rewnifrev2.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of rewnifrev with other constants or assertions; checks a[i] >= i

var SIZE: int;


method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0 
{
  var i: int;
  var a: array<int, int>;
  SIZE := *;
  if SIZE > 1 {
    i := SIZE - 2;
    while i >= 0 {
      a := a[i := i];
      a := a[i + 1 := i + 1];
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
