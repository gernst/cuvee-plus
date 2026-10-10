// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-programs/partial_mod_count_limited_1.c
// SV-COMP array-programs/partial_mod_count_limited_1.yml, translated from benchmarks/sv-comp/dafny/array-programs/partial_mod_count_limited_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int k;
  int R;
  int lim;
  int a[];
  __VERIFIER_assume(0 < N);
  j = 0;
  k = 0;
  lim = __VERIFIER_nondet_int();
  R = 1;
  __VERIFIER_assume(0 < lim && lim < N / R);
  i = 0;
  while (i < N) {
    a[i] = i + 1;
    if (k < lim) {
      a[i] = i % R;
    }
    if (a[i] == 0) {
      k = k + 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 0) {
      j = j + 1;
    }
    assert(j < N / R);
    i = i + 1;
  }
}

