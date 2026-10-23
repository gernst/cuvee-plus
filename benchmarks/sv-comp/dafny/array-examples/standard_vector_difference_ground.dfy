// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-examples/standard_vector_difference_ground.dfy
// SV-COMP array-examples/standard_vector_difference_ground.yml (expected: safe), translated from
// the C program by hand: a and b are filled with arbitrary values and c is their difference element by element
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  var i: int;
  var x: int;
  var tmp: int;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp := *;
    a := a[i := tmp];
    tmp := *;
    b := b[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < N {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert c[x] == a[x] - b[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
