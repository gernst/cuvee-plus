// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/res2.c
// SV-COMP array-fpi/res2.yml, translated from benchmarks/sv-comp/dafny/array-fpi/res2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int sum;
  int a[];
  int b[];
  int c[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  sum = 0;
  i = 0;
  while (i < N) {
    a[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum = sum + a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum = sum + b[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    c[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum = sum + c[i];
    i = i + 1;
  }
  assert(sum <= 3 * N);
}

