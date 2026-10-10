// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/ifcompf.c
// SV-COMP array-fpi/ifcompf.yml, translated from benchmarks/sv-comp/dafny/array-fpi/ifcompf.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  i = 0;
  while (i < N) {
    if (i == 0) {
      a[0] = 0;
    } else {
      a[i] = a[i - 1] + 6;
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
    if (i == 0) {
      c[0] = 0;
    } else {
      c[i] = c[i - 1] + b[i - 1];
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(c[i] == i * i * i);
    i = i + 1;
  }
  result = 1;
  return result;
}

