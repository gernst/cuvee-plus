// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-zilu/benchmark09_conjunctive.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark09_conjunctive.yml (expected: safe), translated from the C program
// by hand: x and y, equal and nonnegative, count down together until x is 0, or one of them is negative, which
// breaks the loop, and y is 0 then
//
// findings: x and y are counters with step -1, and the iteration constraint is the negated test of the break, a
// negated disjunction, which a lemma splits into two constraints, and the lemma of benchmark04_conjunctive on the
// bounds of counters with arbitrary steps, here for the second and third dependency, accelerates them; -split
// splits the disjunctions; closed (no output)
// note: 3 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var x: int;
  var y: int;
  x := *;
  y := *;
  assume x == y && y >= 0;
  while x != 0 {
    x := x - 1;
    y := y - 1;
    if x < 0 || y < 0 {
      break;
    }
  }
  assert y == 0;
}

// remaining goals of -teq -simplify -split -simplify:
// none
