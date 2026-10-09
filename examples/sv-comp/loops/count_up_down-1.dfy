// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/count_up_down-1.dfy
// SV-COMP ReachSafety-Loops/loops/count_up_down-1.yml (expected: safe), translated from the C program by hand: x
// counts down from n, unsigned, to 0, while y counts up, which is n then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var n: int;
  var x: int;
  var y: int;
  n := *;
  assume 0 <= n;
  x := n;
  y := 0;
  while x > 0 {
    x := x - 1;
    y := y + 1;
  }
  assert y == n;
}

// remaining goals of -teq -simplify:
// none
