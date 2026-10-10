// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-new/count_by_nondet.c
// SV-COMP loop-new/count_by_nondet.yml, translated from benchmarks/sv-comp/dafny/loop-new/count_by_nondet.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int k;
  int j;
  __VERIFIER_assume(0 < N);
  i = 0;
  k = 0;
  while (i < N) {
    j = __VERIFIER_nondet_int();
    __VERIFIER_assume(1 <= j && j < N);
    i = i + j;
    k = k + 1;
  }
  assert(k <= N);
}

