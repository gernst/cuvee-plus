// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/bresenham-ll.dfy
// SV-COMP ReachSafety-Loops/nla-digbench/bresenham-ll.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks 2*yx - 2*xy - X + (long long) 2*Y - v == 0; 2*yx - 2*xy -
// X + (long long) 2*Y - v + 2*y == 0

method main() returns (result: int) {
  {
    var X: int;
    var Y: int;
    var x: int;
    var y: int;
    var v: int;
    var xy: int;
    var yx: int;
    X := *;
    Y := *;
    v := 2 * Y - X;
    y := 0;
    x := 0;
    while (1 != 0) {
      yx := Y * x;
      xy := X * y;
      assert 2 * yx - 2 * xy - X + 2 * Y - v == 0;
      if !(x <= X) {
        break;
      }
      if v < 0 {
        v := v + 2 * Y;
      } else {
        v := v + 2 * (Y - X);
        y := y + 1;
      }
      x := x + 1;
    }
    xy := x * y;
    yx := Y * x;
    assert 2 * yx - 2 * xy - X + 2 * Y - v + 2 * y == 0;
    result := 0;
    return;
  }
}
