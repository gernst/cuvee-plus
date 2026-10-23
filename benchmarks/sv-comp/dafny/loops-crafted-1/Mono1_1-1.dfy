// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops-crafted-1/Mono1_1-1.dfy
// SV-COMP loops-crafted-1/Mono1_1-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of Mono1_1-2 with other constants or assertions; checks x == 100000001
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000000

method main() returns (result: int) {
  var N: int;
  var x: int;
  assume 0 < N;
  x := 0;
  while x < N {
    if x < 10000000 {
      x := x + 1;
    } else {
      x := x + 2;
    }
  }
  assert x == N + 1;
}
