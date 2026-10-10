// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-new/nested-1.c
// SV-COMP loop-new/nested-1.yml, translated from benchmarks/sv-comp/dafny/loop-new/nested-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int m;
  int k;
  int i;
  int j;
  n = __VERIFIER_nondet_int();
  m = __VERIFIER_nondet_int();
  __VERIFIER_assume(10 <= n);
  __VERIFIER_assume(10 <= m);
  k = 0;
  i = 0;
  while (i < n) {
    j = 0;
    while (j < m) {
      k = k + 1;
      j = j + 1;
    }
    i = i + 1;
  }
  assert(k >= 100);
}

