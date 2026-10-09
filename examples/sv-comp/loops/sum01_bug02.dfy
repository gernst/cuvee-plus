// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/sum01_bug02.dfy
// SV-COMP ReachSafety-Loops/loops/sum01_bug02.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks sn==((long long) n)*(2) || sn == 0

method main() returns (result: int) {
  var tmp₁: int;
  {
    var i: int;
    var j: int;
    var n: int;
    var sn: int;
    j := 10;
    tmp₁ := *;
    assume 0 <= tmp₁;
    n := tmp₁;
    sn := 0;
    if n == 2147483647 {
      result := 0;
      return;
    }
    i := 1;
    while i <= n {
      if i < j {
        sn := sn + 2;
      }
      j := j - 1;
      i := i + 1;
    }
    assert sn == n * 2 || sn == 0;
  }
}
