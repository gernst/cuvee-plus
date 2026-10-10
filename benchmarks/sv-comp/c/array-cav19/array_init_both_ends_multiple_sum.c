// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_init_both_ends_multiple_sum.c
// SV-COMP array-cav19/array_init_both_ends_multiple_sum.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_init_both_ends_multiple_sum.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int i;
  int sum;
  __VERIFIER_assume(0 < N);
  sum = 0;
  i = 0;
  while (i < N) {
    a[i] = i;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[N - i - 1] = i;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum = sum + (a[i] - b[N - i - 1]);
    i = i + 1;
  }
  assert(sum == 0);
}

