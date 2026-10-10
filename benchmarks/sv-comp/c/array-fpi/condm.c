// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-fpi/condm.c
// SV-COMP array-fpi/condm.yml, translated from benchmarks/sv-comp/dafny/array-fpi/condm.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int i;
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    a[i] = 0;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (N % 2 == 0) {
      a[i] = a[i] + 2;
    } else {
      a[i] = a[i] + 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] % 2 == N % 2);
    i = i + 1;
  }
}

