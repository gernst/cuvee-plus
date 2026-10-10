// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-programs/partial_mod_count_4.dfy
// SV-COMP array-programs/partial_mod_count_4.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of partial_mod_count_1 with other constants or assertions; checks j < (N/8)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var i: int;
  var j: int;
  var a: array<int, int>;
  var R: int;
  N := *;
  assume 0 < N;
  j := 0;
  R := 4;
  i := 0;
  while i < N {
    a := a[i := i + 1];
    if i > (quot(N, 2)) {
      a := a[i := (rem(i, R))];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 0 {
      j := j + 1;
    }
    assert j < (quot(N, 8));
    i := i + 1;
  }
  result := 0;
  return;
}
