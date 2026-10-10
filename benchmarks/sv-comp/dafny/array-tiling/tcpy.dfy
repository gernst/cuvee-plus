// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-tiling/tcpy.dfy
// SV-COMP array-tiling/tcpy.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks acopy[i] == a[i]

var SIZE: int;


method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0 
{
  var tmp₁: int;
  var i: int;
  var a: array<int, int>;
  var acopy: array<int, int>;
  SIZE := *;
  if SIZE > 1 {
    i := 0;
    while i < SIZE {
      tmp₁ := *;
      a := a[i := tmp₁];
      i := i + 1;
    }
    if (rem(SIZE, 2)) != 0 {
      result := 1;
      return;
    }
    assume (rem(SIZE, 2)) == 0;
    i := 0;
    while i < (quot(SIZE, 2)) {
      acopy := acopy[SIZE - i - 1 := a[SIZE - i - 1]];
      acopy := acopy[i := a[i]];
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      assert acopy[i] == a[i];
      i := i + 1;
    }
  }
  result := 1;
  return;
}
