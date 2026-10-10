// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/sqm-if.c
// SV-COMP array-fpi/sqm-if.yml, translated from benchmarks/sv-comp/dafny/array-fpi/sqm-if.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
    assert(a[i] == (i + 1) * (i + 1));
    i = i + 1;
  }
}

