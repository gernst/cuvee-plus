// ./Cuvee.sh -teq -simplify examples/sv-comp/array-programs/partial_mod_count_4.dfy
// SV-COMP ReachSafety-Arrays/array-programs/partial_mod_count_4.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of partial_mod_count_1 with other constants or assertions; checks j < (N/8)
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
  N := *;
  assume 0 < N;
  {
    var i: int;
    var j: int;
    var a: array<int, int>;
    var R: int;
    j := 0;
    R := 4;
    i := 0;
    while i < N {
      a := a[i := i + 1];
      if i > (quotient(N, 2)) {
        a := a[i := (remainder(i, R))];
      }
      i := i + 1;
    }
    i := 0;
    while i < N {
      if a[i] == 0 {
        j := j + 1;
      }
      assert j < (quotient(N, 8));
      i := i + 1;
    }
    result := 0;
    return;
  }
}
