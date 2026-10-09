// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark20_conjunctive.dfy
// SV-COMP loop-zilu/benchmark20_conjunctive.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: sum accumulates i up to n, from nonnegative values, and sum >= 0 is checked
//
// findings: teq.dfy sums i over the counter as (-n + n * n) / 2, which a lemma in the normal form of the simplifier
// (see array-cav19/array_init_var_plus_ind2) states to be nonnegative; closed (no output)

// the sum 0 + 1 + ... + (x - 1) is nonnegative for all integers x, in the normal form of the simplifier (arithmetic,
// not about traces, see array-cav19/array_init_var_plus_ind2); the left-hand side is a comparison
lemma {:rw} {:teq} lemma_1(x: int)
  ensures 0 <= (-x + x * x) / 2

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int, tmp₃: int;
  {
    var i: int, n: int, sum: int;
    tmp₁ := *;
    i := tmp₁;
    tmp₂ := *;
    n := tmp₂;
    tmp₃ := *;
    sum := tmp₃;
    if !(i == 0 && n >= 0 && n <= 100 && sum == 0) {
      result := 0;
      return;
    }
    while i < n {
      sum := sum + i;
      i := i + 1;
    }
    assert sum >= 0;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
