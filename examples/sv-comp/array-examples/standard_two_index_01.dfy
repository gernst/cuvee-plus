// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_two_index_01.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_two_index_01.yml (expected: safe), translated from the C
// program by hand: b is filled with arbitrary values, copied into a with a second index j that runs along i, and a
// and b are compared with both indices again
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the second index j is a counter
// counter(0, 1, n) like i, such that the stores of the copy at ⌊J⌋ are read at the same positions as those of b

method main() {
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var j: int;
  var tmp: int;
  i := 0;
  j := 0;
  while i < 10000 {
    tmp := *;
    b := b[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < 10000 {
    a := a[j := b[i]];
    i := i + 1;
    j := j + 1;
  }
  i := 0;
  j := 0;
  while i < 10000 {
    assert a[j] == b[j];
    i := i + 1;
    j := j + 1;
  }
}

// remaining goals of -teq -simplify:
// none
