// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-programs/partial_mod_count_limited_gen.dfy
// SV-COMP array-programs/partial_mod_count_limited_gen.yml (expected: safe), translated from the
// C program by ./Cuvee.sh -print dfy: a program of the folder; checks j <= ((N*(R-1))/(R*R))
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var tmp₁: int;
  var tmp₂: int;
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
  tmp₂ := *;
  assume 0 <= tmp₂;
  R := tmp₂;
  assume R > 1 && R < 6;
  assume 0 < lim < (quotient(N, R));
  i := 0;
  while i < N {
    a := a[i := i + 1];
    if i > (quotient(N, R)) && k < lim {
      a := a[i := (remainder(i, R))];
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
    assert j <= (quotient(N * (R - 1), R * R));
    i := i + 1;
  }
  result := 0;
  return;
}
