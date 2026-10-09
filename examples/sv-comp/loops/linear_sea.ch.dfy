// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/linear_sea.ch.dfy
// SV-COMP loops/linear_sea.ch.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks linear_search(a,SIZE,3)
// note: the arrays are not initialized (the values of C, which constant(0) gave them), since the result does not
// depend on them

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

var SIZE: int;

var MAX: int;

method linear_search(a: array<int, int>, n: int, q: int) returns (result: int) {
  var j: int;
  j := 0;
  while j < n && a[j] != q {
    j := j + 1;
  }
  if j < SIZE {
    result := 1;
    return;
  } else {
    result := 0;
    return;
  }
}

method main() returns (result: int)
  modifies MAX, SIZE
  requires SIZE == 0 && MAX == 0
{
  var tmp₁: int;
  var tmp₂: int;
  var a: array<int, int>;
  MAX := 100000;
  tmp₁ := *;
  assume 0 <= tmp₁;
  SIZE := (quotient(tmp₁, 8)) + 1;
  if SIZE > 1 && SIZE < MAX {
    a := a[(quotient(SIZE, 2)) := 3];
    tmp₂ := linear_search(a, SIZE, 3);
    assert (tmp₂ != 0);
  }
}
