// ./Cuvee.sh -teq -include teq:aggregation -include teq:arrays -include teq:counters -prove examples/dafny/teq/folds.dfy
// the named folds of traces of the database, each with its read lemma: prefix sums over two counters (scans), a copy
// from both ends (copies), stores guarded by a choice (stores_where), a value in two phases (phases), a shift by one
// position (shifts); the wrong version of the guarded stores remains

method prefix(N: int, B0: array<int, int>) returns (B: array<int, int>)
  requires 1 <= N
  ensures B[N - 1] == B0[0] + N - 1
{
  var i: int;
  B := B0;
  i := 1;
  while i < N
  {
    B[i] := B[i - 1] + 1;
    i := i + 1;
  }
}

method both_ends(M: int, N: int, S: array<int, int>, A0: array<int, int>) returns (A: array<int, int>)
  requires 0 <= N && 2 * N <= M
  ensures forall l: int :: 0 <= l < N ==> A[l] == S[l] && A[M - 1 - l] == S[M - 1 - l]
{
  var i: int;
  A := A0;
  i := 0;
  while i < N
  {
    A[M - 1 - i] := S[M - 1 - i];
    A[i] := S[i];
    i := i + 1;
  }
}

method where(N: int, S: array<int, int>, A0: array<int, int>) returns (A: array<int, int>)
  requires 0 <= N
  ensures forall l: int :: 0 <= l < N ==> A[l] == S[l] || A[l] == A0[l]
{
  var i: int;
  var c: int;
  A := A0;
  i := 0;
  while i < N
  {
    c := *;
    if c != 0 { A[i] := S[i]; }
    i := i + 1;
  }
}

method two_phases() returns (X: int)
  ensures X == 100
{
  X := 0;
  while X < 100
  {
    if X < 10 { X := X + 1; } else { X := X + 2; }
  }
}

method shift(N: int, A0: array<int, int>) returns (A: array<int, int>)
  requires 0 <= N
  ensures forall l: int :: 0 <= l < N ==> A[l] == A0[l + 1]
{
  var i: int;
  A := A0;
  i := 0;
  while i < N
  {
    A[i] := A[i + 1];
    i := i + 1;
  }
}

method where_wrong(N: int, S: array<int, int>, A0: array<int, int>) returns (A: array<int, int>)
  requires 0 <= N
  ensures forall l: int :: 0 <= l < N ==> A[l] == S[l]
{
  var i: int;
  var c: int;
  A := A0;
  i := 0;
  while i < N
  {
    c := *;
    if c != 0 { A[i] := S[i]; }
    i := i + 1;
  }
}
