// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/vogal-2.dfy
// SV-COMP loops/vogal-2.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of vogal-1 with other constants or assertions; checks cont_aux==cont
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 10

// the constant array of the initializers of C, whose values are all x
function constant(x: int): array<int, int>

lemma {:rw} {:teq} constant_1(x: int, i: int)
  ensures constant(x)[i] == x

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  assume 0 < N;
  {
    var string_entrada: array<int, int>;
    var vetor_vogais: array<int, int>;
    var i: int;
    var j: int;
    var cont: int;
    var tam_string: int;
    var n_caracter: int;
    var cont_aux: int;
    vetor_vogais := constant(0)[0 := 97][1 := 65][2 := 101][3 := 69][4 := 105][5 := 73][6 := 111][7 := 79][8 := 117][9 := 85][N := 0];
    i := 0;
    while i < N {
      tmp₁ := *;
      string_entrada := string_entrada[i := tmp₁];
      i := i + 1;
    }
    string_entrada := string_entrada[N - 1 := 0];
    n_caracter := 0;
    while string_entrada[n_caracter] != 0 {
      n_caracter := n_caracter + 1;
    }
    cont := 0;
    i := 0;
    while i < n_caracter {
      j := 0;
      while j < 8 {
        if string_entrada[i] == vetor_vogais[j] {
          cont := cont + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    i := 0;
    cont_aux := 0;
    while string_entrada[i] != 0 {
      j := 0;
      while j < N {
        if string_entrada[i] == vetor_vogais[j] {
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
}
