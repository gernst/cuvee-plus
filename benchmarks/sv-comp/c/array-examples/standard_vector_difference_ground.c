// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_vector_difference_ground.c
// SV-COMP array-examples/standard_vector_difference_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_vector_difference_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int c[];
  int i;
  int x;
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a[i] = tmp;
    tmp = __VERIFIER_nondet_int();
    b[i] = tmp;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    c[i] = a[i] - b[i];
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(c[x] == a[x] - b[x]);
    x = x + 1;
  }
}

