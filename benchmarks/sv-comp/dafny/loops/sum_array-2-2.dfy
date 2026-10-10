// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/sum_array-2-2.dfy
// SV-COMP loops/sum_array-2-2.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks C[i]==A[i]+B[i]

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var M: int;
  var A: array<int, int>;
  var B: array<int, int>;
  var C: array<int, int>;
  var i: int;
  tmp₁ := *;
  assume 0 <= tmp₁;
  M := tmp₁;
  if M > 1000000 {
    result := 0;
    return;
  }
  i := 0;
  while i < M {
    tmp₂ := *;
    A := A[i := tmp₂];
    i := i + 1;
  }
  i := 0;
  while i < M {
    tmp₃ := *;
    B := B[i := tmp₃];
    i := i + 1;
  }
  i := 0;
  while i < M {
    C := C[i := A[i] + B[i]];
    i := i + 1;
  }
  i := 0;
  while i < M {
    assert C[i] == A[i] + B[i];
    i := i + 1;
  }
}
