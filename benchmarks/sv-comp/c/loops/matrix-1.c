// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/matrix-1.c
// SV-COMP loops/matrix-1.yml, translated from benchmarks/sv-comp/dafny/loops/matrix-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int N_LIN;
  int N_COL;
  int j;
  int k;
  int matriz[][];
  int maior;
  N_LIN = 1;
  N_COL = 1;
  maior = __VERIFIER_nondet_int();
  j = 0;
  while (j < N_COL) {
    k = 0;
    while (k < N_LIN) {
      tmp_1 = __VERIFIER_nondet_int();
      matriz[j][k] = tmp_1;
      if (matriz[j][k] >= maior) {
        maior = matriz[j][k];
      }
      k = k + 1;
    }
    j = j + 1;
  }
  assert(matriz[0][0] <= maior);
  result = 0;
  return result;
}

