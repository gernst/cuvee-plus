// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/rewnifrev2.dfy
// SV-COMP array-tiling/rewnifrev2.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of rewnifrev with other constants or assertions; checks a[i] >= i

var SIZE: int;

var MAX: int;

method main() returns (result: int)
  modifies MAX, SIZE
  requires SIZE == 0 && MAX == 0
{
  MAX := 100000;
  {
    var i: int;
    SIZE := *;
    if SIZE > 1 && SIZE < MAX {
      var a: array<int, int>;
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
}
