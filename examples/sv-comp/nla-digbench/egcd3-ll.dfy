// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/egcd3-ll.dfy
// SV-COMP ReachSafety-Loops/nla-digbench/egcd3-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of egcd-ll with other constants or assertions; checks a == y * r + x * p; b == x * q + y *
// s; a == k * b + c; v == b * d; p*x - q*x + r*y - s*y == a

method main() returns (result: int) {
  {
    var x: int;
    var y: int;
    var a: int;
    var b: int;
    var p: int;
    var q: int;
    var r: int;
    var s: int;
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
      var c: int;
      var k: int;
      var temp: int;
      if !(b != 0) {
        break;
      }
      c := a;
      k := 0;
      while (1 != 0) {
        var d: int;
        var v: int;
        if !(c >= b) {
          break;
        }
        d := 1;
        v := b;
        while (1 != 0) {
          assert a == y * r + x * p;
          assert b == x * q + y * s;
          assert a == k * b + c;
          assert v == b * d;
          if !(c >= 2 * v) {
            break;
          }
          d := 2 * d;
          v := 2 * v;
        }
        c := c - v;
        k := k + d;
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
    assert p * x - q * x + r * y - s * y == a;
    result := 0;
    return;
  }
}
