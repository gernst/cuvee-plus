// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-lopstr16/break-2.dfy
// SV-COMP array-lopstr16/break-2.yml (expected: safe), translated from the C program by hand:
// the elements are set to 10 up to the middle, where the loop breaks, and they are checked there
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() {
  var N: int;
  var i: int;
  var s: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    if i > N / 2 {
      break;
    }
    s := s[i := 10];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i <= N / 2 {
      assert s[i] == 10;
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
