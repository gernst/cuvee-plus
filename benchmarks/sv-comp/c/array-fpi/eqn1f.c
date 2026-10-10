// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/eqn1f.c
// SV-COMP array-fpi/eqn1f.yml, translated from benchmarks/sv-comp/dafny/array-fpi/eqn1f.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int i;
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  a[0] = 2;
  b[0] = 1;
  i = 1;
  while (i < N) {
    a[i] = a[i - 1] + 20;
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    b[i] = b[i - 1] + a[i - 1];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(b[i] == i * i + i + 1);
    i = i + 1;
  }
}

