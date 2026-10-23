// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-crafted/zero_sum_const1.dfy
// SV-COMP array-crafted/zero_sum_const1.yml (expected: safe), translated from the C program by hand:
// the array is set to 1, summed up, and subtracted again, which leaves 0 (long is int)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (zero_sum_const2 to _5 are
// variants)

method main() {
  var S: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  S := *;
  if S > 1 {
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
      sum := sum - a[i];
      i := i + 1;
    }
    assert sum == 0;
  }
}

// remaining goals of -teq -simplify:
// none
