// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/fermat2-ll.dfy
// SV-COMP ReachSafety-Loops/nla-digbench/fermat2-ll.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of fermat1-ll with other constants or assertions; checks 4*(A+r) == u*u - v*v -
// 2*u + 2*v; ((long long) 4*A) == u*u - v*v - 2*u + 2*v

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  {
    var A: int;
    var R: int;
    var u: int;
    var v: int;
    var r: int;
    A := *;
    R := *;
    assume (R - 1) * (R - 1) < A;
    assume (remainder(A, 2)) == 1;
    u := 2 * R + 1;
    v := 1;
    r := R * R - A;
    while (1 != 0) {
      assert 4 * (A + r) == u * u - v * v - 2 * u + 2 * v;
      if !(r != 0) {
        break;
      }
      if r > 0 {
        r := r - v;
        v := v + 2;
      } else {
        r := r + u;
        u := u + 2;
      }
    }
    assert 4 * A == u * u - v * v - 2 * u + 2 * v;
    result := 0;
    return;
  }
}
