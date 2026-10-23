// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:series -entry powers -prove -split -prove examples/dafny/teq/series_powers.dfy
// the sum of the cubes of a counter (ps4 of nla-digbench): the expansion of (y + 1)^3 leaves sums of the powers with
// coefficients, which are folded into cubes and squares, whose forward facts in the final value of the counter (the
// variable equal to the number of iterations) close the goal

method powers(bound: int) returns (acc: int, yy: int)
  requires 0 <= bound
  ensures 4 * acc == yy * yy * yy * yy + 2 * yy * yy * yy + yy * yy
{
  var cnt: int;
  cnt := 0;
  yy := 0;
  acc := 0;
  while cnt < bound
  {
    cnt := cnt + 1;
    yy := yy + 1;
    acc := yy * yy * yy + acc;
  }
}
