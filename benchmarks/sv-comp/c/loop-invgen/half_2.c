// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/half_2.c
// SV-COMP loop-invgen/half_2.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/half_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int i;
  int k;
  int j;
  n = __VERIFIER_nondet_int();
  k = n;
  i = 0;
  while (i < n) {
    k = k - 1;
    i = i + 2;
  }
  j = 0;
  while (j < n / 2) {
    assert(k > 0);
    k = k - 1;
    j = j + 1;
  }
}

