// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/sina1.c
// SV-COMP array-fpi/sina1.yml, translated from benchmarks/sv-comp/dafny/array-fpi/sina1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int sum;
  int i;
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  sum = 0;
  i = 0;
  while (i < N) {
    sum = sum + 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = sum;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == N);
    i = i + 1;
  }
}

