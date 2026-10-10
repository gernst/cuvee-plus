// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-lopstr16/partial_lesser_bound-1.dfy
// SV-COMP array-lopstr16/partial_lesser_bound-1.yml (expected: safe), translated from the C program by hand:
// the array is set to 0, then the first half to 10, which is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 10000000

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while i < N / 2 {
    a := a[i := 10];
    i := i + 1;
  }
  i := 0;
  while i < N / 2 {
    assert a[i] == 10;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
