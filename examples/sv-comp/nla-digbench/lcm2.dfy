// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/lcm2.dfy
// SV-COMP ReachSafety-Loops/nla-digbench/lcm2.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of lcm1 with other constants or assertions; checks x*u + y*v == 2*a*b; x*u + y*v == 2*a*b

method main() returns (result: int) {
  {
    var a: int;
    var b: int;
    var x: int;
    var y: int;
    var u: int;
    var v: int;
    a := *;
    assume 0 <= a;
    b := *;
    assume 0 <= b;
    assume a >= 1;
    assume b >= 1;
    assume a <= 65535;
    assume b <= 65535;
    x := a;
    y := b;
    u := b;
    v := a;
    while (1 != 0) {
      assert x * u + y * v == 2 * a * b;
      if !(x != y) {
        break;
      }
      if x > y {
        x := x - y;
        v := v + u;
      } else {
        y := y - x;
        u := u + v;
      }
    }
    assert x * u + y * v == 2 * a * b;
    result := 0;
    return;
  }
}
