// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/ifncomp.c
// SV-COMP array-fpi/ifncomp.yml, translated from benchmarks/sv-comp/dafny/array-fpi/ifncomp.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  int b[];
  int c[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    if (i == 0) {
      a[0] = 6;
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
      c[0] = N;
    } else {
      c[i] = c[i - 1] + b[i - 1];
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(c[i] == N + i * i * i);
    i = i + 1;
  }
}

