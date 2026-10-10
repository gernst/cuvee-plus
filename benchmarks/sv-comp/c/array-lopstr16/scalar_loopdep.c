// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/scalar_loopdep.c
// SV-COMP array-lopstr16/scalar_loopdep.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/scalar_loopdep.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int x;
  int y;
  int a[];
  __VERIFIER_assume(0 < N);
  y = 100;
  i = 0;
  while (i < N) {
    x = y;
    a[i] = y;
    y = y + 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] >= 100);
    i = i + 1;
  }
}

