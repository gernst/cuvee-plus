// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/large_const.c
// SV-COMP loop-invgen/large_const.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/large_const.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int c1;
  int c2;
  int c3;
  int n;
  int v;
  int i;
  int k;
  int j;
  c1 = 4000;
  c2 = 2000;
  c3 = 10000;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n && n < 10);
  k = 0;
  i = 0;
  while (i < n) {
    i = i + 1;
    v = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= v && n < 2);
    if (v == 0) {
      k = k + c1;
    } else if (v == 1) {
      k = k + c2;
    } else {
      k = k + c3;
    }
  }
  j = 0;
  while (j < n) {
    assert(k > 0);
    j = j + 1;
    k = k - 1;
  }
}

