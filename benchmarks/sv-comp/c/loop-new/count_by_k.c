// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-new/count_by_k.c
// SV-COMP loop-new/count_by_k.yml, translated from benchmarks/sv-comp/dafny/loop-new/count_by_k.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int k;
  __VERIFIER_assume(0 < N);
  k = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= k && k <= 10);
  i = 0;
  while (i < N * k) {
    i = i + k;
  }
  assert(i == N * k);
}

