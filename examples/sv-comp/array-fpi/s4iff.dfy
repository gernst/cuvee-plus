// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/s4iff.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/s4iff.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of s4if with other constants or assertions; checks sum[0] == 5*N

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

var N: int;

method main() returns (result: int)
  modifies N
  requires N == 0
{
  {
    var check_size: int, i: int, sum: array<int, int>, a: array<int, int>;
    N := *;
    if N <= 0 {
      result := 1;
      return;
    }
    check_size := if 4 > 5 then 4 else 5;
    assume N <= (quotient(2147483647, check_size));
    sum := sum[0 := 1];
    i := 0;
    while i < N {
      a := a[i := 4];
      i := i + 1;
    }
    i := 0;
    while i < N {
      if a[i] == 4 {
        sum := sum[0 := sum[0] + a[i]];
      } else {
        sum := sum[0 := sum[0] * a[i]];
      }
      i := i + 1;
    }
    assert sum[0] == 5 * N;
    result := 1;
    return;
  }
}
