// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/css2003.c
// SV-COMP loop-lit/css2003.yml, translated from benchmarks/sv-comp/dafny/loop-lit/css2003.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int k;
  __VERIFIER_assume(0 < N);
  i = 1;
  j = 1;
  k = __VERIFIER_nondet_int();
  if (!(0 <= k && k <= 1)) {
    return;
  }
  while (i < N) {
    i = i + 1;
    j = j + k;
    k = k - 1;
    assert(1 <= i + k && i + k <= 2 && i >= 1);
  }
}

