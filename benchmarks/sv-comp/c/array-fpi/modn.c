// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/modn.c
// SV-COMP array-fpi/modn.yml, translated from benchmarks/sv-comp/dafny/array-fpi/modn.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
    a[i] = sum % N;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == 0);
    i = i + 1;
  }
}

