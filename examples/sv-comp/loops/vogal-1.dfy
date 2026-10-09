// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/vogal-1.dfy
// SV-COMP loops/vogal-1.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: a variant of vogal-2 with other constants or assertions; checks cont_aux==cont

// the constant array of the initializers of C, whose values are all x
function constant(x: int): array<int, int>

lemma {:rw} {:teq} constant_1(x: int, i: int)
  ensures constant(x)[i] == x

method main() returns (result: int) {
  var tmp₁: int;
  {
    var input_string: array<int, int>;
    var vogal_array: array<int, int>;
    var i: int;
    var j: int;
    var cont: int;
    var tam_string: int;
    var n_caracter: int;
    var cont_aux: int;
    vogal_array := constant(0)[0 := 97][1 := 65][2 := 101][3 := 69][4 := 105][5 := 73][6 := 111][7 := 79][8 := 117][9 := 85][10 := 0];
    i := 0;
    while i < 5 {
      tmp₁ := *;
      input_string := input_string[i := tmp₁];
      i := i + 1;
    }
    if input_string[5 - 1] != 0 {
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
      while j < 2 {
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
      while j < 2 {
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
}
