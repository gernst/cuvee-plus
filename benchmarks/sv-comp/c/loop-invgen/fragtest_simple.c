// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/fragtest_simple.c
// SV-COMP loop-invgen/fragtest_simple.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/fragtest_simple.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int pvlen;
  int k;
  int n;
  int j;
  int b;
  __VERIFIER_assume(0 < N);
  k = 0;
  i = 0;
  pvlen = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_int();
  while (b != 0 && i <= N) {
    i = i + 1;
    b = __VERIFIER_nondet_int();
  }
  if (i > pvlen) {
    pvlen = i;
  }
  i = 0;
  b = __VERIFIER_nondet_int();
  while (b != 0 && i <= N) {
    i = i + 1;
    k = k + 1;
    b = __VERIFIER_nondet_int();
  }
  j = 0;
  n = i;
  while (true) {
    assert(k >= 0);
    k = k - 1;
    i = i - 1;
    j = j + 1;
    if (j >= n) {
      break;
    }
  }
}

