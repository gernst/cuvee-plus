// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/modp.c
// SV-COMP array-fpi/modp.yml, translated from benchmarks/sv-comp/dafny/array-fpi/modp.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int sum;
  int a[];
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
    assert(a[i] % N == 0);
    i = i + 1;
  }
}

