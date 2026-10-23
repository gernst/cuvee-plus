// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-examples/standard_two_index_01.dfy
// SV-COMP array-examples/standard_two_index_01.yml (expected: safe), translated from the C
// program by hand: b is filled with arbitrary values, copied into a with a second index j that runs along i, and a
// and b are compared with both indices again
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the second index j is a counter
// counter(0, 1, n) like i, such that the stores of the copy at ⌊J⌋ are read at the same positions as those of b
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 10000

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var j: int;
  var tmp: int;
  assume 0 < N;
  i := 0;
  j := 0;
  while i < N {
    tmp := *;
    b := b[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[j := b[i]];
    i := i + 1;
    j := j + 1;
  }
  i := 0;
  j := 0;
  while i < N {
    assert a[j] == b[j];
    i := i + 1;
    j := j + 1;
  }
}

// remaining goals of -teq -simplify:
// none
