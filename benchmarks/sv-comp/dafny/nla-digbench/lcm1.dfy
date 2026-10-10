// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/lcm1.dfy
// SV-COMP nla-digbench/lcm1.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks x*u + y*v == a*b; x*u + y*v == a*b; x*u + y*v == a*b; u*y + v*y ==
// a*b; x == y

method main() returns (result: int) {
  var a: int;
  var b: int;
  var x: int;
  var y: int;
  var u: int;
  var v: int;
  a := *;
  assume 0 <= a;
  b := *;
  assume 0 <= b;
  assume a >= 1;
  assume b >= 1;
  x := a;
  y := b;
  u := b;
  v := 0;
  while (1 != 0) {
    assert x * u + y * v == a * b;
    if !(x != y) {
      break;
    }
    while (1 != 0) {
      assert x * u + y * v == a * b;
      if !(x > y) {
        break;
      }
      x := x - y;
      v := v + u;
    }
    while (1 != 0) {
      assert x * u + y * v == a * b;
      if !(x < y) {
        break;
      }
      y := y - x;
      u := u + v;
    }
  }
  assert u * y + v * y == a * b;
  assert x == y;
  result := 0;
  return;
}
