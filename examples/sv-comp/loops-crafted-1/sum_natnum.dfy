// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/sum_natnum.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/sum_natnum.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: sum accumulates 1, ..., SIZE, and the Gauss sum is checked
//
// findings: the functions truth, quotient, and remainder of the C prelude in the output of -print dfy are written
// as != 0, /, and % on the nonnegative values, and the havoc of unsigned values, printed as spec, as havoc and
// assume; closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

var SIZE: int;

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  SIZE := 40000;
  {
    var i: int, sum: int;
    {
      i := 0;
      sum := 0;
    }
    while i < SIZE {
      i := i + 1;
      sum := sum + i;
    }
    assert sum == ((SIZE * (SIZE + 1)) / (2));
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
