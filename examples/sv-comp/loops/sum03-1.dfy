// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/sum03-1.dfy
// SV-COMP ReachSafety-Loops/loops/sum03-1.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of sum01-2 with other constants or assertions; checks sn==x*(2) || sn == 0

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  {
    var sn: int;
    var loop1: int;
    var n1: int;
    var x: int;
    sn := 0;
    tmp₁ := *;
    assume 0 <= tmp₁;
    loop1 := tmp₁;
    tmp₂ := *;
    assume 0 <= tmp₂;
    n1 := tmp₂;
    x := 0;
    while (1 != 0) {
      if x < 10 {
        sn := sn + 2;
      }
      x := x + 1;
      assert sn == x * 2 || sn == 0;
    }
  }
}
