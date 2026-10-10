// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/eqn3f.c
// SV-COMP array-fpi/eqn3f.yml, translated from benchmarks/sv-comp/dafny/array-fpi/eqn3f.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int i;
  int a[];
  int b[];
  N = __VERIFIER_nondet_int();
  if (N <= 0) {
    result = 1;
    return result;
  }
  a[0] = 6;
  b[0] = 10;
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
  i = 0;
  while (i < N) {
    assert(b[i] == 3 * i * i + 3 * i + 1);
    i = i + 1;
  }
  result = 1;
  return result;
}

