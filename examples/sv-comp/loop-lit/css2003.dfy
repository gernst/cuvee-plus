// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/css2003.dfy
// SV-COMP ReachSafety-Loops/loop-lit/css2003.yml (expected: safe), translated from the C program by hand: i counts
// up, j accumulates k, which counts down from 0 or 1, and 1 <= i + k <= 2 and i >= 1 are checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var j: int;
  var k: int;
  i := 1;
  j := 1;
  k := *;
  if !(0 <= k && k <= 1) {
    return;
  }
  while i < 1000000 {
    i := i + 1;
    j := j + k;
    k := k - 1;
    assert 1 <= i + k && i + k <= 2 && i >= 1;
  }
}

// remaining goals of -teq -simplify:
// none
