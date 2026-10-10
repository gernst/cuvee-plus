// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/prod4br-ll.dfy
// SV-COMP nla-digbench/prod4br-ll.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks q + a * b * p == (long long) x * y; q == (long long) x *
// y; a * b == 0

method main() returns (result: int) {
  var x: int;
  var y: int;
  var a: int;
  var b: int;
  var p: int;
  var q: int;
  x := *;
  y := *;
  assume y >= 1;
  a := x;
  b := y;
  p := 1;
  q := 0;
  while (1 != 0) {
    assert q + a * b * p == x * y;
    if !(a != 0 && b != 0) {
      break;
    }
    if (rem(a, 2)) == 0 && (rem(b, 2)) == 0 {
      a := (quot(a, 2));
      b := (quot(b, 2));
      p := 4 * p;
    } else if (rem(a, 2)) == 1 && (rem(b, 2)) == 0 {
      a := a - 1;
      q := q + b * p;
    } else if (rem(a, 2)) == 0 && (rem(b, 2)) == 1 {
      b := b - 1;
      q := q + a * p;
    } else {
      a := a - 1;
      b := b - 1;
      q := q + (a + b + 1) * p;
    }
  }
  assert q == x * y;
  assert a * b == 0;
  result := 0;
  return;
}
