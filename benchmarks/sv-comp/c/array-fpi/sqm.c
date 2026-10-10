// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-fpi/sqm.c
// SV-COMP array-fpi/sqm.yml, translated from benchmarks/sv-comp/dafny/array-fpi/sqm.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int i;
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  b[0] = 1;
  a[0] = 1;
  i = 1;
  while (i < N) {
    b[i] = b[i - 1] + 2;
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    a[i] = a[i - 1] + b[i - 1] + 2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == (i + 1) * (i + 1));
    i = i + 1;
  }
}

