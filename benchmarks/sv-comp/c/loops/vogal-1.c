// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/vogal-1.c
// SV-COMP loops/vogal-1.yml, translated from benchmarks/sv-comp/dafny/loops/vogal-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int tmp_2;
  int input_string[];
  int vogal_array[];
  int i;
  int j;
  int cont;
  int tam_string;
  int n_caracter;
  int cont_aux;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N / 2) {
    tmp_2 = __VERIFIER_nondet_int();
    vogal_array[i] = tmp_2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    input_string[i] = tmp_1;
    i = i + 1;
  }
  if (input_string[N - 1] != 0) {
    result = 0;
    return result;
  }
  n_caracter = 0;
  while (input_string[n_caracter] != 0) {
    n_caracter = n_caracter + 1;
  }
  cont = 0;
  i = 0;
  while (i < n_caracter) {
    j = 0;
    while (j < N / 2) {
      if (input_string[i] == vogal_array[j]) {
        cont = cont + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  cont_aux = 0;
  while (input_string[i] != 0) {
    j = 0;
    while (j < N / 2) {
      if (input_string[i] == vogal_array[j]) {
        cont_aux = cont_aux + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  assert(cont_aux == cont);
  result = 0;
  return result;
}

