// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-invgen/seq-3.c
// SV-COMP loop-invgen/seq-3.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/seq-3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n0;
  int n1;
  int i0;
  int i1;
  int j1;
  int k;
  i0 = 0;
  k = 0;
  n0 = __VERIFIER_nondet_int();
  n1 = __VERIFIER_nondet_int();
  while (i0 < n0) {
    i0 = i0 + 1;
    k = k + 1;
  }
  i1 = 0;
  while (i1 < n1) {
    i1 = i1 + 1;
    k = k + 1;
  }
  j1 = 0;
  while (j1 < n0 + n1) {
    assert(k > 0);
    j1 = j1 + 1;
    k = k - 1;
  }
}

