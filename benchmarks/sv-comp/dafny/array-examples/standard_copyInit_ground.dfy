// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_copyInit_ground.dfy
// SV-COMP array-examples/standard_copyInit_ground.yml (expected: safe), translated from the C program by hand:
// a is set to 42, copied into b, and b is checked to be 42
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var x: int;
  var a: array<int, int>;
  var b: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := a[i]];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert b[x] == 42;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
