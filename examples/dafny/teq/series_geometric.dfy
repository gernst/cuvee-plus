// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:series -entry geometric -prove examples/dafny/teq/series_geometric.dfy
// a geometric sequence and a geometric series with the same factor z (geo2 of nla-digbench): yy is a power of z, xx
// the fold series, whose forward fact relates (z - 1) * xx + 1 to the same power

method geometric(z: int, bound: int) returns (xx: int, yy: int)
  ensures 1 + xx * z - xx - z * yy == 0
{
  var cnt: int;
  cnt := 1;
  xx := 1;
  yy := 1;
  while cnt < bound
  {
    cnt := cnt + 1;
    xx := xx * z + 1;
    yy := yy * z;
  }
}
