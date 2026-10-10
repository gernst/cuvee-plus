// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_init_var_plus_ind2.c
// SV-COMP array-cav19/array_init_var_plus_ind2.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_init_var_plus_ind2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int k;
  int l;
  int x;
  int a[];
  __VERIFIER_assume(0 < N);
  j = 0;
  k = 0;
  i = 0;
  while (i < N) {
    x = __VERIFIER_nondet_int();
    if (x != 0) {
      break;
    }
    a[i] = j;
    j = j + i;
    k = k - i;
    i = i + 1;
  }
  l = 1;
  while (l < i) {
    assert(a[l] >= k);
    l = l + 1;
  }
}

