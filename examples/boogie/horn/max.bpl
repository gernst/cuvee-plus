// ./Cuvee.sh -chc -entry main -monomorph examples/boogie/horn/max.bpl
// expected: valid
// conditionals, the postcondition of max is inferred

procedure max(x: int, y: int) returns (m: int)
{
  if (x < y) {
    m := y;
  } else {
    m := x;
  }
}

procedure main(x: int, y: int)
{
  var m: int;
  call m := max(x, y);
  assert x <= m && y <= m;
}
