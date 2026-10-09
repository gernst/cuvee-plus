// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/loopv2.dfy
// SV-COMP loops-crafted-1/loopv2.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: i steps by 4 up to n with j = i + 2, then j and k = i step down by 4 while j is even, and
// k is checked to be even
//
// findings: the functions truth, quotient, and remainder of the C prelude in the output of -print dfy are written
// as != 0, /, and % on the nonnegative values, and the havoc of unsigned values, printed as spec, as havoc and
// assume; closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

var SIZE: int;

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  SIZE := 50000001;
  {
    var n: int, i: int, j: int, k: int;
    n := *;
    if !(n <= SIZE) {
      result := 0;
      return;
    }
    i := 0;
    j := 0;
    while i < n {
      i := i + 4;
      j := i + 2;
    }
    k := i;
    while ((j) % (2)) == 0 {
      j := j - 4;
      k := k - 4;
    }
    assert ((k) % (2)) == 0;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
