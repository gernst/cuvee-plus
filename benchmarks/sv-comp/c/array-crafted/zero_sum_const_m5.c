// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-crafted/zero_sum_const_m5.c
// SV-COMP array-crafted/zero_sum_const_m5.yml, translated from benchmarks/sv-comp/dafny/array-crafted/zero_sum_const_m5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int SIZE;

int main(void) {
  int result;
  int i;
  int a[];
  int sum;
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) {
    sum = 0;
    i = 0;
    while (i < SIZE) {
      a[i] = 1;
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
    i = 0;
    while (i < SIZE) {
      sum = sum - a[i];
      i = i + 1;
    }
    assert(sum == 0);
  }
  result = 1;
  return result;
}

