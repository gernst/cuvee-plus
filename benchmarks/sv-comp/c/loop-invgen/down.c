// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/down.c
// SV-COMP loop-invgen/down.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/down.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int k;
  int i;
  int j;
  k = 0;
  i = 0;
  n = __VERIFIER_nondet_int();
  while (i < n) {
    i = i + 1;
    k = k + 1;
  }
  j = n;
  while (j > 0) {
    assert(k > 0);
    j = j - 1;
    k = k - 1;
  }
}

