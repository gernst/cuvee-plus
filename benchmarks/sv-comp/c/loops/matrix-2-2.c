// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/matrix-2-2.c
// SV-COMP loops/matrix-2-2.yml, translated from benchmarks/sv-comp/dafny/loops/matrix-2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int N_LIN;
  int N_COL;
  int j;
  int k;
  int matriz[][];
  int maior;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  N_LIN = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_2);
  N_COL = tmp_2;
  if (N_LIN >= 1000000000 || N_COL >= 1000000000) {
    result = 0;
    return result;
  }
  maior = __VERIFIER_nondet_int();
  j = 0;
  while (j < N_COL) {
    k = 0;
    while (k < N_LIN) {
      tmp_3 = __VERIFIER_nondet_int();
      matriz[j][k] = tmp_3;
      if (matriz[j][k] > maior) {
        maior = matriz[j][k];
      }
      k = k + 1;
    }
    j = j + 1;
  }
  j = 0;
  while (j < N_COL) {
    k = 0;
    while (k < N_LIN) {
      assert(matriz[j][k] < maior);
      k = k + 1;
    }
    j = j + 1;
  }
}

