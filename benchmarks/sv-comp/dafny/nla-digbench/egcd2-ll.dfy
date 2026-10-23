// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/nla-digbench/egcd2-ll.dfy
// SV-COMP nla-digbench/egcd2-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of egcd-ll with other constants or assertions; checks a == k * b + c; a == y*r + x*p; b ==
// x * q + y * s; q*xy + s*yy - q*x - b*y - s*y + b == 0; q*x + s*y == 0; p*x + r*y == a

method main() returns (result: int) {
  var x: int;
  var y: int;
  var a: int;
  var b: int;
  var p: int;
  var q: int;
  var r: int;
  var s: int;
  var c: int;
  var k: int;
  var xy: int;
  var yy: int;
  var temp: int;
  x := *;
  y := *;
  assume x >= 1;
  assume y >= 1;
  a := x;
  b := y;
  p := 1;
  q := 0;
  r := 0;
  s := 1;
  c := 0;
  k := 0;
  xy := x * y;
  yy := y * y;
  while (1 != 0) {
    if !(b != 0) {
      break;
    }
    c := a;
    k := 0;
    while (1 != 0) {
      assert a == k * b + c;
      assert a == y * r + x * p;
      assert b == x * q + y * s;
      assert q * xy + s * yy - q * x - b * y - s * y + b == 0;
      if !(c >= b) {
        break;
      }
      c := c - b;
      k := k + 1;
    }
    a := b;
    b := c;
    temp := p;
    p := q;
    q := temp - q * k;
    temp := r;
    r := s;
    s := temp - s * k;
  }
  assert q * x + s * y == 0;
  assert p * x + r * y == a;
  result := a;
  return;
}
