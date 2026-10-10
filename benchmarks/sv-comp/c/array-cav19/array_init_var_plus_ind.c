// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_init_var_plus_ind.c
// SV-COMP array-cav19/array_init_var_plus_ind.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_init_var_plus_ind.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int j;
  int k;
  int x;
  int N;
  int a[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  j = 0;
  i = 0;
  while (i < N) {
    x = __VERIFIER_nondet_int();
    if (x != 0) {
      break;
    }
    a[i] = j;
    j = j + i;
    i = i + 1;
  }
  k = 1;
  while (k < i) {
    assert(a[k] >= 0);
    k = k + 1;
  }
}

