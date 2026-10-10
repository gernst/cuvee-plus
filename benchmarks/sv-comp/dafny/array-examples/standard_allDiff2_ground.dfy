// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_allDiff2_ground.dfy
// SV-COMP array-examples/standard_allDiff2_ground.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks a[x] != a[y]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var a: array<int, int>;
  var i: int;
  var r: int;
  var j: int;
  var x: int;
  var y: int;
  assume 0 < N;
  r := 1;
  i := 0;
  while i < N {
    tmp₁ := *;
    a := a[i := tmp₁];
    i := i + 1;
  }
  i := 1;
  while i < N && (r != 0) {
    j := i - 1;
    while j >= 0 && (r != 0) {
      if a[i] == a[j] {
        r := 1;
      }
      j := j - 1;
    }
    i := i + 1;
  }
  if (r != 0) {
    x := 0;
    while x < N {
      y := x + 1;
      while y < N {
        assert a[x] != a[y];
        y := y + 1;
      }
      x := x + 1;
    }
  }
  result := 0;
  return;
}
