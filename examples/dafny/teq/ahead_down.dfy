// ./Cuvee.sh -teq -include teq:arrays -include teq:strides -prove examples/dafny/teq/ahead_down.dfy
// a loop down from N - 1 that stores ahead at i - 1 and then at i (rewnifrev of SV-COMP): the guard 1 <= i and the
// cell i - 1 are written over the first counter, k + 2 <= N and N - k - 2, which select_current_trace_ahead_down
// reads (teq:strides); the cell i holds i at the end, so the wrong postcondition with i + 1 remains

method down(N: int) returns (A: array<int, int>)
  requires 2 <= N
  ensures forall l: int :: 0 <= l < N ==> A[l] >= l
{
  var i: int;
  i := N - 1;
  while i >= 0
  {
    if i - 1 >= 0 { A[i - 1] := i - 2; }
    A[i] := i;
    i := i - 1;
  }
}

method wrong(N: int) returns (A: array<int, int>)
  requires 2 <= N
  ensures forall l: int :: 0 <= l < N ==> A[l] >= l + 1
{
  var i: int;
  i := N - 1;
  while i >= 0
  {
    if i - 1 >= 0 { A[i - 1] := i - 2; }
    A[i] := i;
    i := i - 1;
  }
}
