// ./Cuvee.sh -teq -fallback examples/dafny/teq/fallback.dfy
// the fallback encoding of trace equation systems into first-order logic: the traces become uninterpreted functions
// of an index, characterized point-wise, where the guards of the updates need not be complete (break)

method search(a: array<int, int>, n: int) returns (i: int, s: int)
  requires 0 <= n
  ensures 0 <= i <= n
{
  var v: int;
  i := 0;
  s := 0;
  while i < n {
    if a[i] == 0 {
      break;
    }
    v := *;
    s := s + v;
    i := i + 1;
  }
}
