// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_copyInitSum_ground.c
// SV-COMP array-examples/standard_copyInitSum_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_copyInitSum_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int incr;
  int i;
  int x;
  __VERIFIER_assume(0 < N);
  incr = __VERIFIER_nondet_int();
  i = 0;
  while (i < N) {
    a[i] = 42;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[i] = a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[i] = b[i] + incr;
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(b[x] == 42 + incr);
    x = x + 1;
  }
}

