// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/ifeqn1.c
// SV-COMP array-fpi/ifeqn1.yml, translated from benchmarks/sv-comp/dafny/array-fpi/ifeqn1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  int b[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    if (i == 0) {
      a[0] = 2;
    } else {
      a[i] = a[i - 1] + 2;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i == 0) {
      b[0] = 1;
    } else {
      b[i] = b[i - 1] + a[i - 1];
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(b[i] == i * i + i + 1);
    i = i + 1;
  }
}

