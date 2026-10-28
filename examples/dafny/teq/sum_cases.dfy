// ./Cuvee.sh -teq -include teq:aggregation -include teq:arrays -prove examples/dafny/teq/sum_cases.dfy
// stores of 2 or 0 by the parity of the position, then their sum in a cell with a reset at the first position (like
// brs2 of SV-COMP): the values of the stores are a map with two cases, 0 at the first and at the odd positions merged
// into one, whose sum is at most N times the larger value (sum_below); the same in a scalar, where the read
// of the map with cases is a choice nested in the update of the sum, lifted into its cases
// (current_trace_reset_add_keep)

method sum_parity(N: int) returns (T: array<int, int>)
  requires 0 < N
  ensures T[0] <= 2 * N
{
  var A: array<int, int>;
  var i: int;
  i := 0;
  while i < N
  {
    if i % 2 == 0 { A[i] := 2; } else { A[i] := 0; }
    i := i + 1;
  }
  i := 0;
  while i < N
  {
    if i == 0 { T[0] := 0; } else { T[0] := T[0] + A[i]; }
    i := i + 1;
  }
}

method sum_parity_scalar(N: int) returns (T: int)
  requires 0 < N
  ensures T <= 2 * N
{
  var A: array<int, int>;
  var i: int;
  i := 0;
  while i < N
  {
    if i % 2 == 0 { A[i] := 2; } else { A[i] := 0; }
    i := i + 1;
  }
  i := 0;
  while i < N
  {
    if i == 0 { T := 0; } else { T := T + A[i]; }
    i := i + 1;
  }
}
