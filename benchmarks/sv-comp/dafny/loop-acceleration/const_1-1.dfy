// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/const_1-1.dfy
// SV-COMP loop-acceleration/const_1-1.yml (expected: safe), translated from the C program by
// hand: x is set to 0 in each of 1024 iterations, and is 0 then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1024

method main() {
  var N: int;
  var x: int;
  var y: int;
  assume 0 < N;
  x := 1;
  y := 0;
  while y < N {
    x := 0;
    y := y + 1;
  }
  assert x == 0;
}

// remaining goals of -teq -simplify:
// none
