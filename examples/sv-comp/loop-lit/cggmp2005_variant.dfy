// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/cggmp2005_variant.dfy
// SV-COMP ReachSafety-Loops/loop-lit/cggmp2005_variant.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks lo == hi

method main() returns (result: int) {
  {
    var lo: int;
    var mid: int;
    var hi: int;
    lo := 0;
    mid := *;
    if !(mid > 0 && mid <= 1000000) {
      result := 0;
      return;
    }
    hi := 2 * mid;
    while mid > 0 {
      lo := lo + 1;
      hi := hi - 1;
      mid := mid - 1;
    }
    assert lo == hi;
    result := 0;
    return;
  }
}
