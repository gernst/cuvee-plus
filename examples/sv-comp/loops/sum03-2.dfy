// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/sum03-2.dfy
// SV-COMP ReachSafety-Loops/loops/sum03-2.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: sn grows by 2 and x by 1 in an infinite loop, and sn == 2 x or sn == 0 is checked (unsigned int is int)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int;
  {
    var sn: int, loop1: int, n1: int, x: int;
    sn := 0;
    tmp₁ := *;
    assume 0 <= tmp₁;
    loop1 := tmp₁;
    tmp₂ := *;
    assume 0 <= tmp₂;
    n1 := tmp₂;
    x := 0;
    while ((1) != 0) {
      sn := sn + 2;
      x := x + 1;
      assert sn == x * 2 || sn == 0;
    }
  }
}

// remaining goals of -teq -simplify:
// none
