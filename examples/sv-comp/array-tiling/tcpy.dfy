// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/tcpy.dfy
// SV-COMP array-tiling/tcpy.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks acopy[i] == a[i]

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

var SIZE: int;

var MAX: int;

method main() returns (result: int)
  modifies MAX, SIZE
  requires SIZE == 0 && MAX == 0
{
  var tmp₁: int;
  var i: int;
  var a: array<int, int>;
  var acopy: array<int, int>;
  MAX := 100000;
  SIZE := *;
  if SIZE > 1 && SIZE < MAX {
    i := 0;
    while i < SIZE {
      tmp₁ := *;
      a := a[i := tmp₁];
      i := i + 1;
    }
    if (remainder(SIZE, 2)) != 0 {
      result := 1;
      return;
    }
    assume (remainder(SIZE, 2)) == 0;
    i := 0;
    while i < (quotient(SIZE, 2)) {
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
