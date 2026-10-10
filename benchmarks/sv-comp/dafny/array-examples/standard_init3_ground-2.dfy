// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_init3_ground-2.dfy
// SV-COMP array-examples/standard_init3_ground-2.yml (expected: safe), translated from the C
// program by hand: a is initialized three times, to 42, 43, and 44, and is 44 then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the last of the three
// initializations overwrites all positions
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var a: array<int, int>;
  var i: int;
  var x: int;
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
  x := 0;
  while x < N {
    assert a[x] == 44;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
