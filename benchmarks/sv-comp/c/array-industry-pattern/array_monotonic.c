// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-industry-pattern/array_monotonic.c
// SV-COMP array-industry-pattern/array_monotonic.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_monotonic.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  int b[];
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a[i] = tmp;
    if (a[i] == 10) {
      b[i] = 20;
    }
    i = i + 2;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 10) {
      assert(b[i] == 20);
    }
    i = i + 2;
  }
}

