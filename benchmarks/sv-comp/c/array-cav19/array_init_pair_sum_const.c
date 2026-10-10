// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_init_pair_sum_const.c
// SV-COMP array-cav19/array_init_pair_sum_const.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_init_pair_sum_const.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int N;
  int a[];
  int b[];
  int c[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    a[i] = 1;
    b[i] = 2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    c[i] = a[i] + b[i];
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    assert(c[i] >= 3);
    i = i + 1;
  }
}

