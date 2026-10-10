// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/sanfoundry_43_ground.dfy
// SV-COMP array-examples/sanfoundry_43_ground.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of sanfoundry_02_ground with other constants or assertions
// note: the concrete loop bounds are symbolic: N for 100000, which is passed to incrementArray

method incrementArray(src: array<int, int>, dst: array<int, int>, N: int) {
  var dst₁: array<int, int>;
  var i: int;
  dst₁ := dst;
  i := 0;
  while i < N {
    dst₁ := dst₁[i := src[i] + 1];
    i := i + 1;
  }
}

method main() returns (result: int) {
  var N: int;
  var tmp₂: int;
  var src: array<int, int>;
  var dst: array<int, int>;
  var x: int;
  var i: int;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp₂ := *;
    src := src[i := tmp₂];
    i := i + 1;
  }
  incrementArray(src, dst, N);
  x := 0;
  while x < N {
    src := src[x := dst[x] - 1];
    x := x + 1;
  }
  result := 0;
  return;
}
