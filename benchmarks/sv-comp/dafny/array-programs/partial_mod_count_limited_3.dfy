// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-programs/partial_mod_count_limited_3.dfy
// SV-COMP array-programs/partial_mod_count_limited_3.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of partial_mod_count_limited_1 with other constants or assertions;
// checks j < (N/(2*R))+2
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var tmp₁: int;
  var i: int;
  var j: int;
  var k: int;
  var a: array<int, int>;
  var lim: int;
  var R: int;
  N := *;
  assume 0 < N;
  j := 0;
  k := 0;
  tmp₁ := *;
  lim := tmp₁;
  R := 3;
  assume 0 < lim < (quot(N, R));
  i := 0;
  while i < N {
    a := a[i := i + 1];
    if i > (quot(N, 2)) && k < lim {
      a := a[i := (rem(i, R))];
    }
    if a[i] == 0 {
      k := k + 1;
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 0 {
      j := j + 1;
    }
    assert j < (quot(N, 2 * R)) + 2;
    i := i + 1;
  }
  result := 0;
  return;
}
