// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/diff-2-n-u.c
// SV-COMP array-multidimensional/diff-2-n-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/diff-2-n-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int tmp_4;
  int i;
  int j;
  int m;
  int n;
  int A[][];
  int B[][];
  int C[][];
  m = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < m);
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < n);
  i = 0;
  j = 0;
  while (i < m) {
    j = 0;
    while (j < n) {
      tmp_1 = __VERIFIER_nondet_int();
      __VERIFIER_assume(0 <= tmp_1);
      A[i][j] = tmp_1;
      tmp_2 = __VERIFIER_nondet_int();
      __VERIFIER_assume(0 <= tmp_2);
      B[i][j] = tmp_2;
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < m) {
    j = 0;
    while (j < n) {
      tmp_3 = __VERIFIER_nondet_int();
      __VERIFIER_assume(0 <= tmp_3);
      A[i][j] = tmp_3;
      tmp_4 = __VERIFIER_nondet_int();
      __VERIFIER_assume(0 <= tmp_4);
      B[i][j] = tmp_4;
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < m) {
    j = 0;
    while (j < n) {
      C[i][j] = A[i][j] - B[i][j];
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < m) {
    j = 0;
    while (j < n) {
      assert(C[i][j] == A[i][j] - B[i][j]);
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

