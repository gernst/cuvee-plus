// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/init-2-n-u.c
// SV-COMP array-multidimensional/init-2-n-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/init-2-n-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int j;
  int m;
  int n;
  int C;
  int A[][];
  m = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < m);
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < n);
  C = __VERIFIER_nondet_int();
  i = 0;
  while (i < m) {
    j = 0;
    while (j < n) {
      A[i][j] = C;
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < m) {
    j = 0;
    while (j < n) {
      assert(A[i][j] == C);
      j = j + 1;
    }
    i = i + 1;
  }
}

