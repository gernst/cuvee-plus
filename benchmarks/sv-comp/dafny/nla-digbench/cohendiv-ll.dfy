// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/cohendiv-ll.dfy
// SV-COMP nla-digbench/cohendiv-ll.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks b == y*a; x == q*y + r; b == y*a; x == q*y + r; r >= 0; r
// >= 2 * y * a; x == q*y + r

method main() returns (result: int) {
  var x: int;
  var y: int;
  var q: int;
  var r: int;
  var a: int;
  var b: int;
  x := *;
  y := *;
  assume y >= 1;
  q := 0;
  r := x;
  a := 0;
  b := 0;
  while (1 != 0) {
    assert b == y * a;
    assert x == q * y + r;
    if !(r >= y) {
      break;
    }
    a := 1;
    b := y;
    while (1 != 0) {
      assert b == y * a;
      assert x == q * y + r;
      assert r >= 0;
      if !(r >= 2 * b) {
        break;
      }
      assert r >= 2 * y * a;
      a := 2 * a;
      b := 2 * b;
    }
    r := r - b;
    q := q + a;
  }
  assert x == q * y + r;
  result := 0;
  return;
}
