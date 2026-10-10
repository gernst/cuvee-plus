// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/trex02-1.dfy
// SV-COMP loops/trex02-1.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: the global x is decremented by calls of foo, in both branches of a nondeterministic choice, while x > 0, and
// x <= 0 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the calls of foo in the loop, a
// procedure without contract, are summarized by -teq

var x: int;

method foo()
  modifies x
{
  x := x - 1;
}

method main() returns (result: int)
  modifies x
  requires x == 0
{
  var tmp₁: bool;
  var c: bool;
  x := *;
  while x > 0
    modifies x
  {
    tmp₁ := *;
    c := tmp₁;
    if c {
      foo();
    } else {
      foo();
    }
  }
  assert x <= 0;
}

// remaining goals of -teq -simplify:
// none
