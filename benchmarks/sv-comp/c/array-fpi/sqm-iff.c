// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/sqm-iff.c
// SV-COMP array-fpi/sqm-iff.yml, translated from benchmarks/sv-comp/dafny/array-fpi/sqm-iff.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
      b[0] = 1;
    } else {
      b[i] = b[i - 1] + 2;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i == 0) {
      a[0] = 1;
    } else {
      a[i] = a[i - 1] + b[i - 1] + 2;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == i * i);
    i = i + 1;
  }
  result = 1;
  return result;
}

