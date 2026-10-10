// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-crafted/zero_sum_const_m2.c
// SV-COMP array-crafted/zero_sum_const_m2.yml, translated from benchmarks/sv-comp/dafny/array-crafted/zero_sum_const_m2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int sum;
  int a[];
  S = __VERIFIER_nondet_int();
  if (S > 1) {
    sum = 0;
    i = 0;
    while (i < S) {
      a[i] = 1;
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      sum = sum + a[i];
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      sum = sum + a[i];
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      sum = sum - a[i];
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      sum = sum - a[i];
      i = i + 1;
    }
    assert(sum == 0);
  }
}

