// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/matrix-1.dfy
// SV-COMP loops/matrix-1.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: a program of the folder; checks matriz[0][0]<=maior

method main() returns (result: int) {
  var tmp₁: int;
  var N_LIN: int;
  var N_COL: int;
  var j: int;
  var k: int;
  var matriz: array<int, array<int, int>>;
  var maior: int;
  N_LIN := 1;
  N_COL := 1;
  maior := *;
  j := 0;
  while j < N_COL {
    k := 0;
    while k < N_LIN {
      tmp₁ := *;
      matriz := matriz[j := matriz[j][k := tmp₁]];
      if matriz[j][k] >= maior {
        maior := matriz[j][k];
      }
      k := k + 1;
    }
    j := j + 1;
  }
  assert matriz[0][0] <= maior;
  result := 0;
  return;
}
