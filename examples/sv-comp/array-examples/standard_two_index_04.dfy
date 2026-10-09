// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_two_index_04.dfy
// SV-COMP array-examples/standard_two_index_04.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of standard_two_index_01 with other constants or assertions; checks
// a[j] == b[4*j+1]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var j: int;
  assume 0 < N;
  i := 0;
  j := 0;
  while i < N {
    tmp₁ := *;
    b := b[i := tmp₁];
    i := i + 1;
  }
  i := 1;
  while i < N {
    a := a[j := b[i]];
    i := i + 4;
    j := j + 1;
  }
  i := 1;
  j := 0;
  while i < N {
    assert a[j] == b[4 * j + 1];
    i := i + 4;
    j := j + 1;
  }
  result := 0;
  return;
}
