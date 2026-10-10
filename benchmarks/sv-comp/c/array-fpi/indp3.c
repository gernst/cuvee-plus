// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/indp3.c
// SV-COMP array-fpi/indp3.yml, translated from benchmarks/sv-comp/dafny/array-fpi/indp3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    a[i] = (i - 1) * (i - 1);
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] + i;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] + i;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] - 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == i * i);
    i = i + 1;
  }
}

