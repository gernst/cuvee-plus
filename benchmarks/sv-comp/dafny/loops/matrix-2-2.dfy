// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops/matrix-2-2.dfy
// SV-COMP loops/matrix-2-2.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks matriz[j][k]<maior

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var N_LIN: int;
  var N_COL: int;
  var j: int;
  var k: int;
  var matriz: array<int, array<int, int>>;
  var maior: int;
  tmp₁ := *;
  assume 0 <= tmp₁;
  N_LIN := tmp₁;
  tmp₂ := *;
  assume 0 <= tmp₂;
  N_COL := tmp₂;
  if N_LIN >= 1000000000 || N_COL >= 1000000000 {
    result := 0;
    return;
  }
  maior := *;
  j := 0;
  while j < N_COL {
    k := 0;
    while k < N_LIN {
      tmp₃ := *;
      matriz := matriz[j := matriz[j][k := tmp₃]];
      if matriz[j][k] > maior {
        maior := matriz[j][k];
      }
      k := k + 1;
    }
    j := j + 1;
  }
  j := 0;
  while j < N_COL {
    k := 0;
    while k < N_LIN {
      assert matriz[j][k] < maior;
      k := k + 1;
    }
    j := j + 1;
  }
}
