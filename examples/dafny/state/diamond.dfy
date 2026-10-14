// ./Cuvee.sh -teq -prove examples/dafny/state/diamond.dfy
// loop-acceleration/diamond_1-1 of SV-COMP over mathematical integers: the guard y % 2 == 0 does not change in the
// loop, the goal is proved by cases on it (Prove.conditions), the odd case by cases on the remainder y % 2
// (Prove.remainders), which the rational simplex does not enumerate

method diamond(y: int) returns (x: int)
  ensures x % 2 == y % 2
{
  x := 0;
  while x < 99
  {
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + 1;
    }
  }
}
