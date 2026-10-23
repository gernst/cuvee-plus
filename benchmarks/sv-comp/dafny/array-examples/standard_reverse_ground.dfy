// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-examples/standard_reverse_ground.dfy
// SV-COMP array-examples/standard_reverse_ground.yml (expected: safe), translated from the C
// program by hand: a is filled with arbitrary values, b is its reverse, which is checked element by element
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the reads of the copy at 100000
// - x - 1 are resolved by the stores at the counter positions
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var x: int;
  var tmp: int;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp := *;
    a := a[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := a[N - i - 1]];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a[x] == b[N - x - 1];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
