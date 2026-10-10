// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/init-4-n-u.c
// SV-COMP array-multidimensional/init-4-n-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/init-4-n-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  int k;
  int l;
  int m;
  int n;
  int p;
  int q;
  int A[][][][];
  int C;
  m = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < m);
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < n);
  p = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < p);
  q = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < q);
  tmp_1 = __VERIFIER_nondet_int();
  C = tmp_1;
  i = 0;
  j = 0;
  k = 0;
  l = 0;
  while (i < m) {
    j = 0;
    k = 0;
    l = 0;
    while (j < n) {
      k = 0;
      l = 0;
      while (k < p) {
        l = 0;
        while (l < q) {
          A[i][j][k][l] = C;
          l = l + 1;
        }
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  k = 0;
  l = 0;
  while (i < m) {
    j = 0;
    k = 0;
    l = 0;
    while (j < n) {
      k = 0;
      l = 0;
      while (k < p) {
        l = 0;
        while (l < q) {
          assert(A[i][j][k][l] == C);
          l = l + 1;
        }
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

