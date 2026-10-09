// ./Cuvee.sh -verify -print lean examples/dafny/printing/lean_verify.dfy
// the verification conditions of methods are goals, printed in Lean as examples to be proved
method abs(x: int) returns (y: int)
  ensures 0 <= y
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}

method set(a: array<int, int>, i: int) returns (b: array<int, int>)
  ensures b[i] == 1
{
  b := a[i := 1];
}
