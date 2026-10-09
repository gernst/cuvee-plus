// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark11_linear.dfy
// SV-COMP loop-zilu/benchmark11_linear.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x counts up to n from x <= n, and x == n is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (the _abstracted variant is the
// same program with an abstracted loop)

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int;
  {
    var x: int, n: int;
    tmp₁ := *;
    x := tmp₁;
    tmp₂ := *;
    n := tmp₂;
    if !(x == 0 && n > 0) {
      result := 0;
      return;
    }
    while x < n {
      x := x + 1;
    }
    assert x == n;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
