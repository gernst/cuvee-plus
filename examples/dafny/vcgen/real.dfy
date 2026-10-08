// ./Cuvee.sh -verify -z3 examples/dafny/vcgen/real.dfy
// expected: valid
// real arithmetic and decimal literals

method mid(a: real, b: real) returns (c: real)
  requires a < b
  ensures a < c && c < b
{
  c := (a + b) / 2.0;
}

method scale(a: real) returns (b: real)
  requires 0.0 <= a
  ensures b <= a
{
  b := a * 0.75 - -0.125 * 0.0;
}
