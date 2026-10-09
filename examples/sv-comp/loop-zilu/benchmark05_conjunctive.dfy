// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark05_conjunctive.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark05_conjunctive.yml (expected: safe), translated from the C program
// by hand: x counts up to n from below y, and y follows x once x passes it, such that y is n at the end
//
// findings: y follows the counter x once x has caught up with it, a follower, whose current value the lemma states
// as the larger of its initial value and the final value of x, given that it starts at least at x; closed (no
// output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var x: int;
  var y: int;
  var n: int;
  havoc x;
  havoc y;
  havoc n;
  assume x >= 0 && x <= y && y < n;
  while x < n {
    x := x + 1;
    if x > y {
      y := y + 1;
    }
  }
  assert y == n;
}

// remaining goals of -teq -simplify:
// none
