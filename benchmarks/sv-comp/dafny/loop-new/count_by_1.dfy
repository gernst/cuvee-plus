// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-new/count_by_1.dfy
// SV-COMP loop-new/count_by_1.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: i counts to 1000000, which is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() returns (result: int) {
  var N: int;
  var i: int;
  assume 0 < N;
  i := 0;
  while i < N {
    i := i + 1;
  }
  assert i == N;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
