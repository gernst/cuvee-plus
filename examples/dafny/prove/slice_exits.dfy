// ./Cuvee.sh -prove examples/dafny/prove/slice_exits.dfy
// a loop is left where its test does not hold and at the breaks of its body, whose positions are merged: after the
// search, either the key was found, or all positions were searched; the test of the if after it is false in both cases,
// so the branch is unreachable and dropped

method search(len: int, key: int) returns (res: int)
{
  var idx: int;
  var found: bool;
  idx := 0;
  found := false;
  while (idx < len) {
    if (idx == key) {
      found := true;
      break;
    }
    idx := idx + 1;
  }
  if (!found && idx < len) {
    res := -1;
  } else {
    res := idx;
  }
}
