// ./Cuvee.sh -slice examples/dafny/teq/slice_closed_form.dfy
// with -slice, the head of a loop in the simplification of procedures is its trace equation system, simplified before
// the loop, where the counters have closed forms, and attached to the loop as an invariant over the program variables,
// simplified once more, which eliminates the traces; the test after the loop is decided by it

method twice(len: int) returns (res: int)
  requires 0 <= len
{
  var tot: int;
  var idx: int;
  tot := 0;
  idx := 0;
  while (idx < len) {
    tot := tot + 2;
    idx := idx + 1;
  }
  if (tot == 2 * idx) {
    res := tot;
  } else {
    res := -1;
  }
}
