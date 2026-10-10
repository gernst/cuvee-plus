// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/transpose-u.c
// SV-COMP array-multidimensional/transpose-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/transpose-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int k;
  int j;
  int n;
  int A[][];
  int C[][];
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < n);
  i = 0;
  while (i < n) {
    j = 0;
    while (j < n) {
      tmp_1 = __VERIFIER_nondet_int();
      A[i][j] = tmp_1;
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < n) {
    j = 0;
    while (j < n) {
      C[j][i] = A[i][j];
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < n) {
    j = 0;
    while (j < n) {
      assert(C[j][i] == A[i][j]);
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

