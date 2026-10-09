// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ms1.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/ms1.yml (expected: safe), translated from the C program by hand: a[i] is i %
// 1, i.e., 0, and sum adds the elements except the first, which is 0; sum[0] of the one-element array as a scalar
//
// findings: as brs1, with the elements i % 1, which are 0; closed (no output)
// note: 2 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var sum: int;
  N := *;
  assume 0 < N <= 536870911;
  i := 0;
  while i < N {
    a := a[i := i % 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      sum := 0;
    } else {
      sum := sum + a[i];
    }
    i := i + 1;
  }
  assert sum == 0;
}

// remaining goals of -teq -simplify:
// none
