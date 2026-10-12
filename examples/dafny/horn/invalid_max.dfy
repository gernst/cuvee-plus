// ./Cuvee.sh -chc -entry main examples/dafny/horn/invalid_max.dfy
// expected: invalid
// the inferred postcondition of max does not imply that the result is the first argument

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
  assert m == x;
}
