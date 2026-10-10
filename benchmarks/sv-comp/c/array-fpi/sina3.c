// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/sina3.c
// SV-COMP array-fpi/sina3.yml, translated from benchmarks/sv-comp/dafny/array-fpi/sina3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int sum;
  int a[];
  int b[];
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
    b[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum = sum + a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = b[i] + sum;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == N + 1);
    i = i + 1;
  }
}

