// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/copy-3-n-u.c
// SV-COMP array-multidimensional/copy-3-n-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/copy-3-n-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  int k;
  int m;
  int n;
  int p;
  int A[][][];
  int B[][][];
  m = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < m);
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < n);
  p = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < p);
  i = 0;
  j = 0;
  k = 0;
  while (i < m) {
    j = 0;
    k = 0;
    while (j < n) {
      k = 0;
      while (k < p) {
        tmp_1 = __VERIFIER_nondet_int();
        B[i][j][k] = tmp_1;
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  k = 0;
  while (i < m) {
    j = 0;
    k = 0;
    while (j < n) {
      k = 0;
      while (k < p) {
        A[i][j][k] = B[i][j][k];
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  k = 0;
  while (i < m) {
    j = 0;
    k = 0;
    while (j < n) {
      k = 0;
      while (k < p) {
        assert(A[i][j][k] == B[i][j][k]);
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

