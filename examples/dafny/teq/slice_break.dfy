// ./Cuvee.sh -slice examples/dafny/teq/slice_break.dfy
// a loop that the body may leave by break: after it, the test is not known not to hold, but its invariant is,
// which decides the test after the loop; the iteration constraint states that the earlier values differ from key

method search(len: int, key: int) returns (res: int)
  requires 0 <= len
{
  var idx: int;
  idx := 0;
  while (idx < len) {
    if (idx == key) {
      break;
    }
    idx := idx + 1;
  }
  if (idx <= len) {
    res := idx;
  } else {
    res := -1;
  }
}
