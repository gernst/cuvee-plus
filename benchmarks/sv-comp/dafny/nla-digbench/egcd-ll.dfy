// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/egcd-ll.dfy
// SV-COMP nla-digbench/egcd-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks 1 == p * s - r * q; a == y * r + x * p; b == x * q + y * s; a - b ==
// 0; p*x + r*y - b == 0; q*r - p*s + 1 == 0; q*x + s*y - b == 0

method main() returns (result: int) {
  var a: int;
  var b: int;
  var p: int;
  var q: int;
  var r: int;
  var s: int;
  var x: int;
  var y: int;
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
  while (1 != 0) {
    assert 1 == p * s - r * q;
    assert a == y * r + x * p;
    assert b == x * q + y * s;
    if !(a != b) {
      break;
    }
    if a > b {
      a := a - b;
      p := p - q;
      r := r - s;
    } else {
      b := b - a;
      q := q - p;
      s := s - r;
    }
  }
  assert a - b == 0;
  assert p * x + r * y - b == 0;
  assert q * r - p * s + 1 == 0;
  assert q * x + s * y - b == 0;
  result := 0;
  return;
}
