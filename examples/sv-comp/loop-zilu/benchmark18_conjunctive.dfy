// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark18_conjunctive.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark18_conjunctive.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: i and k count up together to n, and i == k == n is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int, tmp₃: int;
  {
    var i: int, k: int, n: int;
    havoc tmp₁;
    i := tmp₁;
    havoc tmp₂;
    k := tmp₂;
    havoc tmp₃;
    n := tmp₃;
    if !(i == 0 && k == 0 && n > 0) {
      result := 0;
      return;
    }
    while i < n {
      i := i + 1;
      k := k + 1;
    }
    assert i == k == n;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
