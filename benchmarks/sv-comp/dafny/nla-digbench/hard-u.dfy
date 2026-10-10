// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/hard-u.dfy
// SV-COMP nla-digbench/hard-u.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks q == 0; r == A; d == B * p; A == q*B + r; d == B*p; A == d*q + r; B
// == d

method main() returns (result: int) {
  var A: int;
  var B: int;
  var r: int;
  var d: int;
  var p: int;
  var q: int;
  A := *;
  assume 0 <= A;
  B := *;
  assume 0 <= B;
  assume B >= 1;
  r := A;
  d := B;
  p := 1;
  q := 0;
  while (1 != 0) {
    assert q == 0;
    assert r == A;
    assert d == B * p;
    if !(r >= d) {
      break;
    }
    d := 2 * d;
    p := 2 * p;
  }
  while (1 != 0) {
    assert A == q * B + r;
    assert d == B * p;
    if !(p != 1) {
      break;
    }
    d := (quot(d, 2));
    p := (quot(p, 2));
    if r >= d {
      r := r - d;
      q := q + p;
    }
  }
  assert A == d * q + r;
  assert B == d;
  result := 0;
  return;
}
