// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-new/gauss_sum.c
// SV-COMP loop-new/gauss_sum.yml, translated from benchmarks/sv-comp/dafny/loop-new/gauss_sum.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int sum;
  int i;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(1 <= n);
  sum = 0;
  i = 1;
  while (i <= n) {
    sum = sum + i;
    i = i + 1;
  }
  assert(2 * sum == n * (n + 1));
}

