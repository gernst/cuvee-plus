// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/jm2006.dfy
// SV-COMP ReachSafety-Loops/loop-lit/jm2006.yml (expected: safe), translated from the C program by hand: x and y
// count down from i and j, nonnegative, until x is 0, and y is 0 then if i == j
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): x and y are counters with step
// -1, the exit x == 0 gives the number of iterations i

method main() {
  var i: int;
  var j: int;
  var x: int;
  var y: int;
  i := *;
  j := *;
  assume i >= 0 && j >= 0;
  x := i;
  y := j;
  while x != 0 {
    x := x - 1;
    y := y - 1;
  }
  if i == j {
    assert y == 0;
  }
}

// remaining goals of -teq -simplify:
// none
