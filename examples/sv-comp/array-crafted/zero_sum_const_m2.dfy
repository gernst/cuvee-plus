// ./Cuvee.sh -teq -simplify examples/sv-comp/array-crafted/zero_sum_const_m2.dfy
// SV-COMP array-crafted/zero_sum_const_m2.yml (expected: safe), translated from the C program by hand:
// the array is set to 1, summed up twice, and subtracted twice, which leaves 0 (long long is int)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (zero_sum_const_m3 to _m5,
// zero_sum2 to 5, and zero_sum_m3 to _m5 are variants of this and of zero_sum1 and zero_sum_m2)

method main() {
  var S: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  S := *;
  if S > 1 && S < 100000 {
    sum := 0;
    i := 0;
    while i < S {
      a := a[i := 1];
      i := i + 1;
    }
    i := 0;
    while i < S {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while i < S {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while i < S {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while i < S {
      sum := sum - a[i];
      i := i + 1;
    }
    assert sum == 0;
  }
}

// remaining goals of -teq -simplify:
// none
