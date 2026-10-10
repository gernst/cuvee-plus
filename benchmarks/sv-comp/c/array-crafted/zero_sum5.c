// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-crafted/zero_sum5.c
// SV-COMP array-crafted/zero_sum5.yml, translated from benchmarks/sv-comp/dafny/array-crafted/zero_sum5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int SIZE;

int main(void) {
  int result;
  int tmp_2;
  int i;
  int a[];
  int sum;
  int i_1;
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) {
    sum = 0;
    i_1 = 0;
    while (i_1 < SIZE) {
      tmp_2 = __VERIFIER_nondet_int();
      a[i_1] = tmp_2;
      i_1 = i_1 + 1;
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
      sum = sum + a[i];
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

