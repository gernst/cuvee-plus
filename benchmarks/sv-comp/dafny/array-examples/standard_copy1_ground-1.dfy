// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_copy1_ground-1.dfy
// SV-COMP array-examples/standard_copy1_ground-1.yml (expected: safe), translated from the C
// program by hand: a1 is filled with arbitrary values and copied into a2, which then equals a1
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the copy is stores at the
// counter positions
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a: int;
  var i: int;
  var x: int;
  var tmp: int;
  assume 0 < N;
  a := 0;
  while a < N {
    tmp := *;
    a1 := a1[a := tmp];
    a := a + 1;
  }
  i := 0;
  while i < N {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a1[x] == a2[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
