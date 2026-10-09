// ./Cuvee.sh -teq -simplify examples/sv-comp/array-programs/partial_mod_count_limited_base.dfy
// SV-COMP array-programs/partial_mod_count_limited_base.yml (expected: safe), translated from
// the C program by ./Cuvee.sh -print dfy: a program of the folder; checks j < 2
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

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
  N := *;
  assume 0 < N;
  {
    var i: int;
    var j: int;
    var k: int;
    var a: array<int, int>;
    var R: int;
    j := 0;
    k := 0;
    tmp₁ := *;
    R := tmp₁;
    assume R > 0;
    i := 0;
    while i < N {
      a := a[i := i + 1];
      if i > (quotient(N, 2)) && k < 1 {
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
      assert j < 2;
      i := i + 1;
    }
    result := 0;
    return;
  }
}
