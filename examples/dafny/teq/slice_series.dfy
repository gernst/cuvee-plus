// ./Cuvee.sh -slice -include teq:aggregation -include teq:arithmetic -include teq:counters -include teq:series examples/dafny/teq/slice_series.dfy
// the invariant of a sum of squares is the fold squares of the module series; the test after the loop stays, since
// the closed form of the fold is not linear

method squares_below(len: int) returns (res: int)
  requires 0 <= len
{
  var tot: int;
  var idx: int;
  tot := 0;
  idx := 0;
  while (idx < len) {
    tot := tot + idx * idx;
    idx := idx + 1;
  }
  if (0 <= tot) {
    res := tot;
  } else {
    res := -1;
  }
}
