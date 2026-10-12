// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_9.dfy
// SV-COMP loops-crafted-1/mono-crafted_9.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mono-crafted_1 with other constants or assertions; checks y==x
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000
// note: assumes 500000 <= N, as the C version: the property depends on the original constant, which the symbolic bound
// generalizes, and fails without (benchmarks/sv-comp/c/false-verdicts.md, group 1)

method main() returns (result: int) {
  var N: int;
  var x: int;
  var y: int;
  assume 500000 <= N;
  x := 0;
  y := 500000;
  while x < N {
    if x < 500000 {
      x := x + 1;
    } else {
      x := x + 1;
      y := y + 1;
    }
  }
  assert y == x;
  result := 0;
  return;
}
