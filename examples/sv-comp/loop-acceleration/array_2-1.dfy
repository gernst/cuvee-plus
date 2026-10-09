// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/array_2-1.dfy
// SV-COMP loop-acceleration/array_2-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array_1-1 with other constants or assertions; checks A[2048/2] != B[2048/2]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 2048

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var tmp₂: int;
  assume 0 < N;
  {
    var A: array<int, int>;
    var B: array<int, int>;
    var i: int;
    var tmp: int;
    i := 0;
    while i < N {
      tmp₁ := *;
      A := A[i := tmp₁];
      tmp₂ := *;
      B := B[i := tmp₂];
      i := i + 1;
    }
    i := 0;
    while i < N {
      tmp := A[i];
      B := B[i := tmp];
      i := i + 1;
    }
    assert A[1024] != B[1024];
  }
}
