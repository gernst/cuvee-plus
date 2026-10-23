// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops/nec20.dfy
// SV-COMP loops/nec20.yml (expected: unsafe), translated from the C program by ./Cuvee.sh -print
// dfy: a variant of nec11 with other constants or assertions; checks j<1025

var b: int;

method main() returns (result: int)
  requires b == 0
{
  var N: int;
  var tmp₁: bool;
  var k: bool;
  var i: int;
  var n: int;
  var j: int;
  var a: array<int, int>;
  assume 1 < N;
  tmp₁ := *;
  k := tmp₁;
  if k {
    n := 0;
  } else {
    n := N - 1;
  }
  i := 0;
  j := *;
  assume 0 <= j;
  while i <= n {
    i := i + 1;
    j := j + 2;
  }
  a := a[i := 0];
  assert j < N + 1;
  a := a[j := 0];
  a := a[b := 0];
  if b >= 0 && b < N - 1 {
    a := a[b := 1];
  } else {
    a := a[(rem(b, N - 1)) := 1];
  }
  result := 1;
  return;
}
