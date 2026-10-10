// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/array_3-2.dfy
// SV-COMP loop-acceleration/array_3-2.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array_1-1 with other constants or assertions; checks i <= 1024 / 2
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1024

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var A: array<int, int>;
  var i: int;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp₁ := *;
    A := A[i := tmp₁];
    i := i + 1;
  }
  i := 0;
  while i < N && A[i] != 0 {
    {}
    i := i + 1;
  }
  assert i <= 512;
}
