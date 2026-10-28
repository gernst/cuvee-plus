// ./Cuvee.sh -teq -include teq:arrays -include teq:strides -prove examples/dafny/teq/strides.dfy
// stores of adjacent cells at a stride fold into strides₂ and strides₃ (teq:strides), whose values the matcher
// synthesizes as maps, with the cases of the update where they differ: a stride of 3 at the offset 1, conditional
// stores by a guard that does not depend on the iteration (like pr2 of SV-COMP), values chosen in each iteration and
// replaced if they are the default (like pnr2), and the wrong postcondition of the latter, which remains

method offset(N: int, v: int) returns (A: array<int, int>)
  requires 0 <= N
  ensures forall l: int :: 0 <= l < N ==> A[3 * l + 1] == l && A[3 * l + 2] == v
{
  var i: int;
  i := 0;
  while i < N
  {
    A[3 * i + 1] := i;
    A[3 * i + 2] := v;
    i := i + 1;
  }
}

method guarded(N: int, M: int) returns (A: array<int, int>)
  requires 0 <= N
  ensures forall l: int :: 0 <= l < 2 * N ==> A[l] >= M || A[l] == 0
{
  var i: int;
  i := 0;
  while i < N
  {
    if 7 >= M { A[2 * i] := 7; } else { A[2 * i] := 0; }
    if 3 >= M { A[2 * i + 1] := 3; } else { A[2 * i + 1] := 0; }
    i := i + 1;
  }
}

method defaults(N: int, C: int, D: int) returns (A: array<int, int>)
  requires 0 <= N && C != D
  ensures forall l: int :: 0 <= l < N ==> A[2 * l] != C && A[2 * l + 1] != C
{
  var i: int;
  var u: int;
  var w: int;
  i := 0;
  while i < N
  {
    u := *;
    w := *;
    if u != C { A[2 * i] := u; } else { A[2 * i] := D; }
    if w != C { A[2 * i + 1] := w; } else { A[2 * i + 1] := D; }
    i := i + 1;
  }
}

method defaults_wrong(N: int, C: int, D: int) returns (A: array<int, int>)
  requires 0 <= N
  ensures forall l: int :: 0 <= l < N ==> A[2 * l] != C && A[2 * l + 1] != C
{
  var i: int;
  var u: int;
  var w: int;
  i := 0;
  while i < N
  {
    u := *;
    w := *;
    if u != C { A[2 * i] := u; } else { A[2 * i] := D; }
    if w != C { A[2 * i + 1] := w; } else { A[2 * i + 1] := D; }
    i := i + 1;
  }
}
