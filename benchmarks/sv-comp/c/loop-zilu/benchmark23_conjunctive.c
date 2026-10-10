// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark23_conjunctive.c
// SV-COMP loop-zilu/benchmark23_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark23_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  __VERIFIER_assume(0 < N);
  i = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  __VERIFIER_assume(i == 0 && j == 0);
  while (i < N) {
    j = j + 2;
    i = i + 1;
  }
  assert(j == 2 * N);
}

