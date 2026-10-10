// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-fpi/condnf.c
// SV-COMP array-fpi/condnf.yml, translated from benchmarks/sv-comp/dafny/array-fpi/condnf.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  int tmp;
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a[i] = tmp;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] > N) {
      a[i] = a[i];
    } else {
      a[i] = N;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] <= N);
    i = i + 1;
  }
}

