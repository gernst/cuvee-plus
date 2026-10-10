// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-fpi/pcomp.c
// SV-COMP array-fpi/pcomp.yml, translated from benchmarks/sv-comp/dafny/array-fpi/pcomp.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  int b[];
  int c[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  a[0] = 6;
  b[0] = 1;
  c[0] = 0;
  i = 1;
  while (i < N) {
    a[i] = a[i - 1] + 6;
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    b[i] = b[i - 1] + a[i - 1];
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    c[i] = c[i - 1] + b[i - 1];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(c[i] == i * i * i);
    i = i + 1;
  }
}

