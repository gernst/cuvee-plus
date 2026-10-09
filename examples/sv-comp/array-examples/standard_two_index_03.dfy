// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_two_index_03.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_two_index_03.yml (expected: safe), translated from the C program by hand:
// as standard_two_index_02 with the step 3 and the bound 10000
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (standard_two_index_04 to _09 are
// variants)

method main() {
  var i: int;
  var j: int;
  var v: int;
  var a: array<int, int>;
  var b: array<int, int>;
  i := 0;
  j := 0;
  while i < 10000 {
    v := *;
    b := b[i := v];
    i := i + 1;
  }
  i := 1;
  while i < 10000 {
    a := a[j := b[i]];
    i := i + 3;
    j := j + 1;
  }
  i := 1;
  j := 0;
  while i < 10000 {
    assert a[j] == b[3 * j + 1];
    i := i + 3;
    j := j + 1;
  }
}

// remaining goals of -teq -simplify:
// none
