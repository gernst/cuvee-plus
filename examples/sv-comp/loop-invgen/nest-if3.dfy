// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/nest-if3.dfy
// SV-COMP ReachSafety-Loops/loop-invgen/nest-if3.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks 1<=i

method main() returns (result: int) {
  var tmp₁: int;
  {
    var i: int;
    var k: int;
    var n: int;
    var l: int;
    n := *;
    l := *;
    if !(l > 0) {
      result := 0;
      return;
    }
    if !(l < 1000000) {
      result := 0;
      return;
    }
    if !(n < 1000000) {
      result := 0;
      return;
    }
    k := 1;
    while k < n {
      i := l;
      while i < n {
        assert 1 <= i;
        i := i + 1;
      }
      tmp₁ := *;
      if (tmp₁ != 0) {
        l := l + 1;
      }
      k := k + 1;
    }
  }
}
