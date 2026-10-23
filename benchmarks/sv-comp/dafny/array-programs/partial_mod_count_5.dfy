// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-programs/partial_mod_count_5.dfy
// SV-COMP array-programs/partial_mod_count_5.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of partial_mod_count_1 with other constants or assertions; checks j < (N/10)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000
// note: assumes N % 10 == 0, as the C version: the property depends on the original constant, which the symbolic bound
// generalizes, and fails without (benchmarks/sv-comp/c/false-verdicts.md, group 1)

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
  assume 0 < N && rem(N, 10) == 0;
  j := 0;
  R := 5;
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
    assert j < (quot(N, 10));
    i := i + 1;
  }
  result := 0;
  return;
}
