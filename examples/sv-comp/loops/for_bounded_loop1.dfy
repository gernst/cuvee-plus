// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/for_bounded_loop1.dfy
// SV-COMP ReachSafety-Loops/loops/for_bounded_loop1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks x==0; x!=0; x==0

method main() returns (result: int) {
  var tmp₁: int;
  {
    var i: int;
    var x: int;
    var y: int;
    var n: int;
    i := 0;
    x := 0;
    y := 0;
    tmp₁ := *;
    n := tmp₁;
    if !(n > 0) {
      result := 0;
      return;
    }
    i := 0;
    while i < n {
      x := x - y;
      assert x == 0;
      y := *;
      if !(y != 0) {
        result := 0;
        return;
      }
      x := x + y;
      assert x != 0;
      i := i + 1;
    }
    assert x == 0;
  }
}
