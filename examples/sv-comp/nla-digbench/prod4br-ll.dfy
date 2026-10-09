// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/prod4br-ll.dfy
// SV-COMP ReachSafety-Loops/nla-digbench/prod4br-ll.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks q + a * b * p == (long long) x * y; q == (long long) x *
// y; a * b == 0

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  {
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
      if (remainder(a, 2)) == 0 && (remainder(b, 2)) == 0 {
        a := (quotient(a, 2));
        b := (quotient(b, 2));
        p := 4 * p;
      } else if (remainder(a, 2)) == 1 && (remainder(b, 2)) == 0 {
        a := a - 1;
        q := q + b * p;
      } else if (remainder(a, 2)) == 0 && (remainder(b, 2)) == 1 {
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
}
