// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/pnr4.dfy
// SV-COMP array-tiling/pnr4.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of pnr2 with other constants or assertions; checks a[i]!=DEFAULTVAL

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method ReadFromPort() returns (result: int) {
  var tmp₁: int;
  {
    var x: int;
    tmp₁ := *;
    x := tmp₁;
    result := x;
    return;
  }
}

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
    var value: int;
    var a: array<int, int>;
    var DEFAULTVAL: int;
    var FIXEDVAL: int;
    DEFAULTVAL := 0;
    FIXEDVAL := 10;
    if (remainder(SIZE, 4)) != 0 {
      result := 1;
      return;
    }
    assume (remainder(SIZE, 4)) == 0;
    i := 1;
    while i <= (quotient(SIZE, 4)) {
      value := ReadFromPort();
      if value != DEFAULTVAL {
        a := a[i * 4 - 4 := value];
      } else {
        a := a[i * 4 - 4 := FIXEDVAL];
      }
      value := ReadFromPort();
      if value != DEFAULTVAL {
        a := a[i * 4 - 3 := value];
      } else {
        a := a[i * 4 - 3 := FIXEDVAL];
      }
      value := ReadFromPort();
      if value != DEFAULTVAL {
        a := a[i * 4 - 2 := value];
      } else {
        a := a[i * 4 - 2 := FIXEDVAL];
      }
      value := ReadFromPort();
      if value != DEFAULTVAL {
        a := a[i * 4 - 1 := value];
      } else {
        a := a[i * 4 - 1 := FIXEDVAL];
      }
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      assert a[i] != DEFAULTVAL;
      i := i + 1;
    }
  }
  result := 1;
  return;
}
