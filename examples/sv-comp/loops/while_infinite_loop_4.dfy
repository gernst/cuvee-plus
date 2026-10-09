// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/while_infinite_loop_4.dfy
// SV-COMP ReachSafety-Loops/loops/while_infinite_loop_4.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of while_infinite_loop_1 with other constants or assertions; checks x==0; x==0

var x: int;

method eval()
  modifies x
{
  while (1 != 0)
    modifies x
  {
    x := 1;
    break;
  }
  return;
}

method main() returns (result: int)
  modifies x
  requires x == 0
{
  x := 0;
  while (1 != 0)
    modifies x
  {
    eval();
    assert x == 0;
  }
  assert x == 0;
  result := 0;
  return;
}
