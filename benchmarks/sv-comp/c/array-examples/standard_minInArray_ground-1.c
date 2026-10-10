// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_minInArray_ground-1.c
// SV-COMP array-examples/standard_minInArray_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_minInArray_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int x;
  int v;
  int min;
  int a[];
  __VERIFIER_assume(0 < N);
  min = 0;
  j = 0;
  while (j < N) {
    v = __VERIFIER_nondet_int();
    a[j] = v;
    j = j + 1;
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
    assert(a[x] > min);
    x = x + 1;
  }
}

