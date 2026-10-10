// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_maxInArray_ground.c
// SV-COMP array-examples/standard_maxInArray_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_maxInArray_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int max;
  int i;
  int x;
  int j;
  int tmp;
  __VERIFIER_assume(0 < N);
  max = 0;
  j = 0;
  while (j < N) {
    tmp = __VERIFIER_nondet_int();
    a[j] = tmp;
    j = j + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] > max) {
      max = a[i];
    }
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(a[x] <= max);
    x = x + 1;
  }
}

