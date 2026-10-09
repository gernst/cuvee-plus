// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/nec20.dfy
// SV-COMP loops/nec20.yml (expected: unsafe), translated from the C program by ./Cuvee.sh -print
// dfy: a variant of nec11 with other constants or assertions; checks j<1025

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

var b: int;

method main() returns (result: int)
  requires b == 0
{
  var tmp₁: bool;
  var k: bool;
  var i: int;
  var n: int;
  var j: int;
  var a: array<int, int>;
  tmp₁ := *;
  k := tmp₁;
  if k {
    n := 0;
  } else {
    n := 1023;
  }
  i := 0;
  j := *;
  assume 0 <= j;
  if j > 10000 {
    result := 0;
    return;
  }
  while i <= n {
    i := i + 1;
    j := j + 2;
  }
  a := a[i := 0];
  assert j < 1025;
  a := a[j := 0];
  a := a[b := 0];
  if b >= 0 && b < 1023 {
    a := a[b := 1];
  } else {
    a := a[(remainder(b, 1023)) := 1];
  }
  result := 1;
  return;
}
