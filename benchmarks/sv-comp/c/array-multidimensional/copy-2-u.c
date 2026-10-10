// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/copy-2-u.c
// SV-COMP array-multidimensional/copy-2-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/copy-2-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  int n;
  int A[][];
  int B[][];
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < n);
  i = 0;
  j = 0;
  while (i < n) {
    j = 0;
    while (j < n) {
      tmp_1 = __VERIFIER_nondet_int();
      B[i][j] = tmp_1;
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < n) {
    j = 0;
    while (j < n) {
      A[i][j] = B[i][j];
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < n) {
    j = 0;
    while (j < n) {
      assert(A[i][j] == B[i][j]);
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

