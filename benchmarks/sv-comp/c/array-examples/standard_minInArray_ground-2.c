// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_minInArray_ground-2.c
// SV-COMP array-examples/standard_minInArray_ground-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_minInArray_ground-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int min;
  int i;
  int x;
  int tmp;
  __VERIFIER_assume(0 < N);
  min = 0;
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a[i] = tmp;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] < min) {
      min = a[i];
    }
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(a[x] >= min);
    x = x + 1;
  }
}

