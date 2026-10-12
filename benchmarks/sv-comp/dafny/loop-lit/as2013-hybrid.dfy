// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-lit/as2013-hybrid.dfy
// SV-COMP loop-lit/as2013-hybrid.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks 0 <= i; i <= 10
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 10
// note: assumes 10 <= N, as the C version: the property depends on the original constant, which the symbolic bound
// generalizes, and fails without (benchmarks/sv-comp/c/false-verdicts.md, group 1)

method main() returns (result: int) {
  var N: int;
  var i: int;
  var j: int;
  assume 10 <= N;
  i := 0;
  while (1 != 0) {
    i := i + 1;
    j := 0;
    while j < N {
      assert 0 <= i;
      assert i <= N;
      j := j + 1;
    }
    if i > 9 {
      i := 0;
    }
  }
  result := 0;
  return;
}
