// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-crafted/zero_sum_m2.c
// SV-COMP array-crafted/zero_sum_m2.yml, translated from benchmarks/sv-comp/dafny/array-crafted/zero_sum_m2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int SIZE;
  int a[];
  int sum;
  int i;
  int tmp;
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) {
    sum = 0;
    i = 0;
    while (i < SIZE) {
      tmp = __VERIFIER_nondet_int();
      a[i] = tmp;
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      sum = sum + a[i];
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      sum = sum + a[i];
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      sum = sum - a[i];
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      sum = sum - a[i];
      i = i + 1;
    }
    assert(sum == 0);
  }
}

