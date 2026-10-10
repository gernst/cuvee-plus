// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/brs1.c
// SV-COMP array-fpi/brs1.yml, translated from benchmarks/sv-comp/dafny/array-fpi/brs1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  int sum;
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    if (i % 1 == 0) {
      a[i] = 1;
    } else {
      a[i] = 0;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i == 0) {
      sum = 0;
    } else {
      sum = sum + a[i];
    }
    i = i + 1;
  }
  assert(sum <= N);
}

