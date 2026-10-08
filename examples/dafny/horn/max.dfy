// ./Cuvee.sh -chc examples/dafny/horn/max.dfy
// expected: valid
// procedures with a body have no contract, their pre- and postconditions are inferred

method max(x: int, y: int) returns (m: int)
{
  if x <= y {
    m := y;
  } else {
    m := x;
  }
}

method main(x: int, y: int)
{
  var m: int;
  m := max(x, y);
  assert x <= m && y <= m;
}
