// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-zilu/benchmark04_conjunctive.c
// SV-COMP loop-zilu/benchmark04_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark04_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int k;
  int j;
  int n;
  k = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(n >= 1 && k >= n && j == 0);
  while (j <= n - 1) {
    j = j + 1;
    k = k - 1;
  }
  assert(k >= 0);
}

