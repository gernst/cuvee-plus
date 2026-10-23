// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops/string-1.dfy
// SV-COMP loops/string-1.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: a variant of string-2 with other constants or assertions; checks found == 0 || found == 1
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 5 (MAX)

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var tmp₂: int;
  var string_A: array<int, int>;
  var string_B: array<int, int>;
  var i: int;
  var j: int;
  var nc_A: int;
  var nc_B: int;
  var found: int;
  assume 0 < N;
  found := 0;
  i := 0;
  while i < N {
    tmp₁ := *;
    string_A := string_A[i := tmp₁];
    i := i + 1;
  }
  if string_A[N - 1] != 0 {
    result := 0;
    return;
  }
  i := 0;
  while i < N {
    tmp₂ := *;
    string_B := string_B[i := tmp₂];
    i := i + 1;
  }
  if string_B[N - 1] != 0 {
    result := 0;
    return;
  }
  nc_A := 0;
  while string_A[nc_A] != 0 {
    nc_A := nc_A + 1;
  }
  nc_B := 0;
  while string_B[nc_B] != 0 {
    nc_B := nc_B + 1;
  }
  if !(nc_B >= nc_A) {
    result := 0;
    return;
  }
  j := 0;
  i := j;
  while i < nc_A && j < nc_B {
    if string_A[i] == string_B[j] {
      i := i + 1;
      j := j + 1;
    } else {
      i := i - j + 1;
      j := 0;
    }
  }
  found := (if j > nc_B - 1 then 1 else 0);
  assert found == 0 || found == 1;
  result := 0;
  return;
}
