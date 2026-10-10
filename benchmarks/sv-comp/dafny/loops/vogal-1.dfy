// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/vogal-1.dfy
// SV-COMP loops/vogal-1.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: a variant of vogal-2 with other constants or assertions; checks cont_aux==cont
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 5 (MAX), hence N / 2 for MAX/2
// note: the vowels of the C program, a constant array, are arbitrary values of the entries that the loops read,
// filled by a loop, since the counts compare the same entries

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var tmp₂: int;
  var input_string: array<int, int>;
  var vogal_array: array<int, int>;
  var i: int;
  var j: int;
  var cont: int;
  var tam_string: int;
  var n_caracter: int;
  var cont_aux: int;
  assume 0 < N;
  i := 0;
  while i < quot(N, 2) {
    tmp₂ := *;
    vogal_array := vogal_array[i := tmp₂];
    i := i + 1;
  }
  i := 0;
  while i < N {
    tmp₁ := *;
    input_string := input_string[i := tmp₁];
    i := i + 1;
  }
  if input_string[N - 1] != 0 {
    result := 0;
    return;
  }
  n_caracter := 0;
  while input_string[n_caracter] != 0 {
    n_caracter := n_caracter + 1;
  }
  cont := 0;
  i := 0;
  while i < n_caracter {
    j := 0;
    while j < quot(N, 2) {
      if input_string[i] == vogal_array[j] {
        cont := cont + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  cont_aux := 0;
  while input_string[i] != 0 {
    j := 0;
    while j < quot(N, 2) {
      if input_string[i] == vogal_array[j] {
        cont_aux := cont_aux + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert cont_aux == cont;
  result := 0;
  return;
}
