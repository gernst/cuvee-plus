// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/eqn2.c
// SV-COMP array-fpi/eqn2.yml, translated from benchmarks/sv-comp/dafny/array-fpi/eqn2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  int b[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  a[0] = 4;
  b[0] = 1;
  i = 1;
  while (i < N) {
    a[i] = a[i - 1] + 4;
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    b[i] = b[i - 1] + a[i - 1];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(b[i] == 2 * i * i + 2 * i + 1);
    i = i + 1;
  }
}

