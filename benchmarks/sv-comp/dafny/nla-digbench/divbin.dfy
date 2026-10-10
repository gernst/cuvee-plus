// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/divbin.dfy
// SV-COMP nla-digbench/divbin.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks A == q * b + r; A == q * b + r

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

method main() returns (result: int) {
  var A: int;
  var B: int;
  var q: int;
  var r: int;
  var b: int;
  A := *;
  assume 0 <= A;
  B := *;
  assume 0 <= B;
  assume B >= 1;
  q := 0;
  r := A;
  b := B;
  while (1 != 0) {
    if !(r >= b) {
      break;
    }
    b := 2 * b;
  }
  while (1 != 0) {
    assert A == q * b + r;
    if !(b != B) {
      break;
    }
    q := 2 * q;
    b := (quotient(b, 2));
    if r >= b {
      q := q + 1;
      r := r - b;
    }
  }
  assert A == q * b + r;
  result := 0;
  return;
}
