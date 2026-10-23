// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/s3if.dfy
// SV-COMP array-fpi/s3if.yml (expected: safe), translated from the C program by hand: a is set
// to 3, and its elements are added to sum if they are 3, which gives 3 N (s4if, s5if are variants)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (s4if, s5if are variants)

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  N := *;
  assume 0 < N;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 3];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 3 {
      sum := sum + a[i];
    } else {
      sum := sum * a[i];
    }
    i := i + 1;
  }
  assert sum == 3 * N;
}

// remaining goals of -teq -simplify:
// none
