// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/dijkstra-u.dfy
// SV-COMP nla-digbench/dijkstra-u.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks r < 2 * p + q; p*p + r*q == n*q; h * h * h - 12 * h * n *
// q + 16 * n * p * q - h * q * q - 4 * p * q * q + 12 * h * q * r - 16 * p * q * r == 0; h * h * n - 4 * h * n * p
// + 4 * (n * n) * q - n * q * q - h * h * r + 4 * h * p * r - 8 * n * q * r + q * q * r + 4 * q * r * r == 0; h * h
// * p - 4 * h * n * q + 4 * n * p * q - p * q * q + 4 * h * q * r - 4 * p * q * r == 0; p * p - n * q + q * r == 0;
// h*h*h - 12*h*n + 16*n*p + 12*h*r - 16*p*r - h - 4*p == 0; p*p - n + r == 0; h*h*p - 4*h*n + 4*n*p + 4*h*r - 4*p*r
// - p == 0

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

method main() returns (result: int) {
  var n: int;
  var p: int;
  var q: int;
  var r: int;
  var h: int;
  n := *;
  assume 0 <= n;
  p := 0;
  q := 1;
  r := n;
  h := 0;
  while (1 != 0) {
    if !(q <= n) {
      break;
    }
    q := 4 * q;
  }
  while (1 != 0) {
    assert r < 2 * p + q;
    assert p * p + r * q == n * q;
    assert
      h * h * h - 12 * h * n * q + 16 * n * p * q - h * q * q - 4 * p * q * q
        + 12 * h * q * r
        - 16 * p * q * r
        == 0;
    assert
      h * h * n - 4 * h * n * p + 4 * (n * n) * q - n * q * q - h * h * r
        + 4 * h * p * r
        - 8 * n * q * r
        + q * q * r
        + 4 * q * r * r
        == 0;
    assert
      h * h * p - 4 * h * n * q + 4 * n * p * q - p * q * q + 4 * h * q * r
        - 4 * p * q * r
        == 0;
    assert p * p - n * q + q * r == 0;
    if !(q != 1) {
      break;
    }
    q := (quotient(q, 4));
    h := p + q;
    p := (quotient(p, 2));
    if r >= h {
      p := p + q;
      r := r - h;
    }
  }
  assert
    h * h * h - 12 * h * n + 16 * n * p + 12 * h * r - 16 * p * r - h - 4 * p
      == 0;
  assert p * p - n + r == 0;
  assert h * h * p - 4 * h * n + 4 * n * p + 4 * h * r - 4 * p * r - p == 0;
  result := 0;
  return;
}
