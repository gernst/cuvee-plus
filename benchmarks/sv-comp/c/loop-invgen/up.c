// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/up.c
// SV-COMP loop-invgen/up.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/up.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int i;
  int k;
  int j;
  i = 0;
  k = 0;
  n = __VERIFIER_nondet_int();
  while (i < n) {
    i = i + 1;
    k = k + 1;
  }
  j = 0;
  while (j < n) {
    assert(k > 0);
    j = j + 1;
    k = k - 1;
  }
}

