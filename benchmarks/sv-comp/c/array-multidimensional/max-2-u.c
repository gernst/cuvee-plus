// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/max-2-u.c
// SV-COMP array-multidimensional/max-2-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/max-2-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  int m;
  int n;
  int A[][];
  int max;
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
      A[i][j] = tmp_1;
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  max = A[0][0];
  while (i < n) {
    j = 0;
    while (j < n) {
      if (A[i][j] > max) {
        max = A[i][j];
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < n) {
    j = 0;
    while (j < n) {
      assert(A[i][j] <= max);
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

