// ./Cuvee.sh -verify -z3 examples/dafny/vcgen/abs.dfy
// expected: valid
// conditional without else branch, statement-level assertion

method abs(x: int) returns (y: int)
  ensures 0 <= y
{
  y := x;
  if y < 0 {
    y := -y;
  }
  assert 0 <= y;
}
