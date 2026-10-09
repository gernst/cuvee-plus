// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_init8_ground-1.dfy
// SV-COMP array-examples/standard_init8_ground-1.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of standard_init1_ground-1 with other constants or assertions; checks
// a[x] == 48
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var a: array<int, int>;
    var i: int;
    var x: int;
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
    i := 0;
    while i < N {
      a := a[i := 47];
      i := i + 1;
    }
    i := 0;
    while i < N {
      a := a[i := 48];
      i := i + 1;
    }
    i := 0;
    while i < N {
      a := a[i := 49];
      i := i + 1;
    }
    x := 0;
    while x < N {
      assert a[x] == 48;
      x := x + 1;
    }
    result := 0;
    return;
  }
}
