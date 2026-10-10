// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_init5_ground-1.dfy
// SV-COMP array-examples/standard_init5_ground-1.yml (expected: safe), translated from the C program by hand:
// the array is set to 42, 43, 44, 45, 46 by five loops, and checked to be 46
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output), in about the time of the copies
// (see the summary, performance)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var x: int;
  var a: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := 43];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := 44];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := 45];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := 46];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a[x] == 46;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
