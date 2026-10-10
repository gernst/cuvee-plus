// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_min_and_copy_shift_sum_add.c
// SV-COMP array-cav19/array_min_and_copy_shift_sum_add.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_min_and_copy_shift_sum_add.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int k;
  int a[];
  int b[];
  j = __VERIFIER_nondet_int();
  k = 0;
  N = __VERIFIER_nondet_int();
  i = 0;
  while (i < N) {
    if (j > a[i]) {
      j = a[i];
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[i] = a[i] - j;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    k = k + b[i] + i;
    i = i + 1;
  }
  assert(k >= 0);
}

