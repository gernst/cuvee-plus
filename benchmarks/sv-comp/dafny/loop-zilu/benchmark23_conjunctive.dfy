// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-zilu/benchmark23_conjunctive.dfy
// SV-COMP loop-zilu/benchmark23_conjunctive.yml (expected: safe), translated from the C program
// by hand: j counts by 2 while i counts to 100, and j is 200 then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary values that keep the verdict: N for 100, the assertion j ==
// 200 is j == 2 * N

method main() {
  var N: int;
  var i: int;
  var j: int;
  assume 0 < N;
  i := *;
  j := *;
  assume i == 0 && j == 0;
  while i < N {
    j := j + 2;
    i := i + 1;
  }
  assert j == 2 * N;
}

// remaining goals of -teq -simplify:
// none
