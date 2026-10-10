// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/init-3-u.c
// SV-COMP array-multidimensional/init-3-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/init-3-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  int k;
  int n;
  int A[][][];
  int C;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < n);
  tmp_1 = __VERIFIER_nondet_int();
  C = tmp_1;
  i = 0;
  j = 0;
  k = 0;
  while (i < n) {
    j = 0;
    k = 0;
    while (j < n) {
      k = 0;
      while (k < n) {
        A[i][j][k] = C;
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  k = 0;
  while (i < n) {
    j = 0;
    k = 0;
    while (j < n) {
      k = 0;
      while (k < n) {
        assert(A[i][j][k] == C);
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

