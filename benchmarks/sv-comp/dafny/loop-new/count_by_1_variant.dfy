// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-new/count_by_1_variant.dfy
// SV-COMP loop-new/count_by_1_variant.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: i counts to 1000000 by the test i != 1000000, checked to stay at most 1000000
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() returns (result: int) {
  var N: int;
  var i: int;
  assume 0 < N;
  i := 0;
  while i != N {
    assert i <= N;
    i := i + 1;
  }
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
