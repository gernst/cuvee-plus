// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/divbin2.dfy
// SV-COMP ReachSafety-Loops/nla-digbench/divbin2.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of divbin with other constants or assertions; checks A == q * b + r; A == q * b + r

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

method main() returns (result: int) {
  {
    var A: int;
    var B: int;
    var q: int;
    var r: int;
    var b: int;
    A := *;
    assume 0 <= A;
    B := 1;
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
}
