// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/nested9.dfy
// SV-COMP loop-invgen/nested9.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of nested6 with other constants or assertions; checks k-i <= 2*n

var __BLAST_NONDET: int;

method main() returns (result: int)
  requires __BLAST_NONDET == 0
{
  {
    var i: int;
    var j: int;
    var k: int;
    var n: int;
    var l: int;
    var m: int;
    n := *;
    m := *;
    l := *;
    if !(-1000000 < n < 1000000) {
      result := 0;
      return;
    }
    if !(-1000000 < m < 1000000) {
      result := 0;
      return;
    }
    if !(-1000000 < l < 1000000) {
      result := 0;
      return;
    }
    if 3 * n <= m + l {} else {
      result := 0;
      return;
    }
    i := 0;
    while i < n {
      j := 2 * i;
      while j < 3 * i {
        k := i;
        while k < j {
          assert k - i <= 2 * n;
          k := k + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    result := 0;
    return;
  }
}
