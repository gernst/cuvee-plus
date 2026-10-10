// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_tripl_access_init_const.c
// SV-COMP array-cav19/array_tripl_access_init_const.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_tripl_access_init_const.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i <= N) {
    a[3 * i] = 0;
    a[3 * i + 1] = 0;
    a[3 * i + 2] = 0;
    i = i + 1;
  }
  i = 0;
  while (i <= 3 * N) {
    assert(a[i] >= 0);
    i = i + 1;
  }
}

