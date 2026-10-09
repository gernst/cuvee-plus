// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/afnp2014.dfy
// SV-COMP ReachSafety-Loops/loop-lit/afnp2014.yml (expected: safe), translated from the C program by hand: x
// accumulates the values of y, which counts from 0, for a nondeterministic number of iterations below 1000, and
// stays at least y, the nondeterministic test as a variable c that is havocked before each test
//
// findings: y is a counter, x accumulates it, which teq.dfy accelerates to 1 + (n * n - n) / 2; the
// nondeterministic test is a havocked variable, whose trace takes the values of a sequence; the remaining goal is
// arithmetic, x >= y, since (n - 1) * (n - 2) is not negative for integers, which the lemma states in the normal
// form of the simplifier; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var x: int;
  var y: int;
  var c: int;
  x := 1;
  y := 0;
  c := *;
  while y < 1000 && c != 0 {
    x := x + y;
    y := y + 1;
    c := *;
  }
  assert x >= y;
}

// remaining goals of -teq -simplify:
// none
