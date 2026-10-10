// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_reverse_ground.c
// SV-COMP array-examples/standard_reverse_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_reverse_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int i;
  int x;
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a[i] = tmp;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[i] = a[N - i - 1];
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(a[x] == b[N - x - 1]);
    x = x + 1;
  }
}

