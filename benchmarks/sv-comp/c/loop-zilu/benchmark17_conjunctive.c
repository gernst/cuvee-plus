// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark17_conjunctive.c
// SV-COMP loop-zilu/benchmark17_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark17_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int k;
  int n;
  i = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(i == 0 && k == 0);
  while (i < n) {
    i = i + 1;
    k = k + 1;
  }
  assert(k >= n);
}

