// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/bhmr2007.dfy
// SV-COMP loop-lit/bhmr2007.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks a + b == 3*n

method main() returns (result: int) {
  var tmp₁: int;
  var i: int;
  var n: int;
  var a: int;
  var b: int;
  i := 0;
  a := 0;
  b := 0;
  n := *;
  if !(n >= 0 && n <= 1000000) {
    result := 0;
    return;
  }
  while i < n {
    tmp₁ := *;
    if (tmp₁ != 0) {
      a := a + 1;
      b := b + 2;
    } else {
      a := a + 2;
      b := b + 1;
    }
    i := i + 1;
  }
  assert a + b == 3 * n;
  result := 0;
  return;
}
