// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/partial_lesser_bound-1.c
// SV-COMP array-lopstr16/partial_lesser_bound-1.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/partial_lesser_bound-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    a[i] = 0;
    i = i + 1;
  }
  i = 0;
  while (i < N / 2) {
    a[i] = 10;
    i = i + 1;
  }
  i = 0;
  while (i < N / 2) {
    assert(a[i] == 10);
    i = i + 1;
  }
}

