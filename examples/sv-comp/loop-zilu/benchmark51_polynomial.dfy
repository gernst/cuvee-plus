// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark51_polynomial.dfy
// SV-COMP loop-zilu/benchmark51_polynomial.yml (expected: safe), translated from the C program by
// hand: x between 0 and 50 moves down by 1, or up by 1 from 0, for an arbitrary number of iterations, and stays
// between 0 and 50; the increment for x > 50 never applies; the nondeterministic test as a variable c that is
// havocked before each test
//
// findings: x stays in the interval [0, 50], into which each of the three cases maps it; the lemma states this
// inductive invariant for an interval that contains the initial value, with quantified side conditions on the
// cases, which the simplifier decides once instantiated, and the conjunction of both bounds as its left-hand side,
// which binds both; closed (no output); a variant with the initial range up to 60, and one that decrements by 2,
// are not closed
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var x: int;
  var c: int;
  x := *;
  assume x >= 0 && x <= 50;
  c := *;
  while c != 0 {
    if x > 50 {
      x := x + 1;
    }
    if x == 0 {
      x := x + 1;
    } else {
      x := x - 1;
    }
    c := *;
  }
  assert x >= 0 && x <= 50;
}

// remaining goals of -teq -simplify:
// none
