// ./Cuvee.sh -simplify examples/simplify/statements.dfy
// programs are simplified statement by statement
method m(x: int) returns (y: int)
  requires 0 <= x + 0
{
  var z: int;
  y := y;
  if 1 < 2 { y := (x + 1) * 1; } else { y := 0; }
  while false { y := 2; }
}
