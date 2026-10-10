// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/vogal-2.c
// SV-COMP loops/vogal-2.yml, translated from benchmarks/sv-comp/dafny/loops/vogal-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int tmp_2;
  int string_entrada[];
  int vetor_vogais[];
  int i;
  int j;
  int cont;
  int tam_string;
  int n_caracter;
  int cont_aux;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < 10) {
    tmp_2 = __VERIFIER_nondet_int();
    vetor_vogais[i] = tmp_2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    string_entrada[i] = tmp_1;
    i = i + 1;
  }
  string_entrada[N - 1] = 0;
  n_caracter = 0;
  while (string_entrada[n_caracter] != 0) {
    n_caracter = n_caracter + 1;
  }
  cont = 0;
  i = 0;
  while (i < n_caracter) {
    j = 0;
    while (j < 8) {
      if (string_entrada[i] == vetor_vogais[j]) {
        cont = cont + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  cont_aux = 0;
  while (string_entrada[i] != 0) {
    j = 0;
    while (j < 10) {
      if (string_entrada[i] == vetor_vogais[j]) {
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

