// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/trex02-2.dfy
// SV-COMP ReachSafety-Loops/loops/trex02-2.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of trex01-1 with other constants or assertions; checks x==0

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
  x := *;
  while x > 0
    modifies x
  {
    var c: bool;
    tmp₁ := *;
    c := tmp₁;
    if c {
      foo();
    } else {
      foo();
    }
  }
  assert x == 0;
}
