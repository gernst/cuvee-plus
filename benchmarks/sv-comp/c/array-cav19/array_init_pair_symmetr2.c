// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_init_pair_symmetr2.c
// SV-COMP array-cav19/array_init_pair_symmetr2.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_init_pair_symmetr2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int x;
  int y;
  int a[];
  int b[];
  int c[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    __VERIFIER_assume(y < N && y > -N);
    __VERIFIER_assume(x < N && x > -N);
    __VERIFIER_assume(x > y);
    a[i] = x;
    b[i] = y;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    c[i] = a[i] - b[i];
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    assert(c[i] > 0);
    i = i + 1;
  }
}

