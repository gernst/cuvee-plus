// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_two_index_02.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_two_index_02.yml (expected: safe), translated from the C program by hand:
// a[j] = b[i] for i = 1, 3, 5, ... and j = 0, 1, 2, ..., and a[j] == b[2 j + 1] is checked
// (standard_two_index_03 to _09 are variants with other steps and bounds)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the second loop reads b at the
// counter 1, 3, 5, ... and stores at the counter of j

method main() {
  var i: int;
  var j: int;
  var v: int;
  var a: array<int, int>;
  var b: array<int, int>;
  i := 0;
  j := 0;
  while i < 100000 {
    v := *;
    b := b[i := v];
    i := i + 1;
  }
  i := 1;
  while i < 100000 {
    a := a[j := b[i]];
    i := i + 2;
    j := j + 1;
  }
  i := 1;
  j := 0;
  while i < 100000 {
    assert a[j] == b[2 * j + 1];
    i := i + 2;
    j := j + 1;
  }
}

// remaining goals of -teq -simplify:
// none
