// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/ifeqn3f.c
// SV-COMP array-fpi/ifeqn3f.yml, translated from benchmarks/sv-comp/dafny/array-fpi/ifeqn3f.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  i = 0;
  while (i < N) {
    if (i == 0) {
      a[0] = 6;
    } else {
      a[i] = a[i - 1] + 3;
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
    assert(b[i] == 3 * i * i + 3 * i + 1);
    i = i + 1;
  }
  result = 1;
  return result;
}

