// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_init_nondet_vars.c
// SV-COMP array-cav19/array_init_nondet_vars.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_init_nondet_vars.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int j;
  int n;
  int k;
  int a[];
  j = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(j > 0);
  i = 1;
  while (i < n) {
    k = __VERIFIER_nondet_int();
    __VERIFIER_assume(k > 0);
    a[i] = i + j + k;
    i = i + 1;
  }
  i = 1;
  while (i < n) {
    assert(a[i] >= i + 2);
    i = i + 1;
  }
}

