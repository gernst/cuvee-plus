// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/ncompf.c
// SV-COMP array-fpi/ncompf.yml, translated from benchmarks/sv-comp/dafny/array-fpi/ncompf.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int i;
  int a[];
  int b[];
  int c[];
  N = __VERIFIER_nondet_int();
  if (N <= 0) {
    result = 1;
    return result;
  }
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
    assert(c[i] == N + i * i * i);
    i = i + 1;
  }
  result = 1;
  return result;
}

