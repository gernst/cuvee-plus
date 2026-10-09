// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-new/count_by_1_variant.dfy
// SV-COMP ReachSafety-Loops/loop-new/count_by_1_variant.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: i counts to 1000000 by the test i != 1000000, checked to stay at most 1000000
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() returns (result: int) {
  {
    var i: int;
    {
      i := 0;
      while i != 1000000 {
        {
          assert i <= 1000000;
        }
        i := i + 1;
      }
    }
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
