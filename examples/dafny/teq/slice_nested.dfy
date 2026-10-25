// ./Cuvee.sh -slice examples/dafny/teq/slice_nested.dfy
// the inner loop gets its own system from the values at its entry, which are those of the head of the outer loop;
// its invariant quantifies the number of iterations of the outer loop, which no program variable holds

method nested(len: int, wid: int) returns (res: int)
  requires 0 <= len && 0 <= wid
{
  var cnt: int;
  var row: int;
  var col: int;
  cnt := 0;
  row := 0;
  while (row < len) {
    col := 0;
    while (col < wid) {
      cnt := cnt + 1;
      col := col + 1;
    }
    row := row + 1;
  }
  res := cnt;
}
