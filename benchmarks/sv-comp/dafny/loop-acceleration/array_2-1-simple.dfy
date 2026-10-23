// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/array_2-1-simple.dfy
// SV-COMP loop-acceleration/array_2-1-simple.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks A[2048/2] != B[2048/2]
// note: the arrays are not initialized (the values of C, which constant(0) gave them), and the assertion A[2048/2]
// != B[2048/2] of C is A[N / 2] != B[N / 2], in the middle of the copied range, such that the result does not
// depend on the initial values
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 2048

method main() returns (result: int) {
  var N: int;
  var A: array<int, int>;
  var B: array<int, int>;
  var i: int;
  var tmp: int;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp := A[i];
    B := B[i := tmp];
    i := i + 1;
  }
  assert A[quot(N, 2)] != B[quot(N, 2)];
}
