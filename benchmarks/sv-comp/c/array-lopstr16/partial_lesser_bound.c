// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/partial_lesser_bound.c
// SV-COMP array-lopstr16/partial_lesser_bound.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/partial_lesser_bound.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  _Bool a[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    a[i] = false;
    i = i + 1;
  }
  i = 0;
  while (i < N / 2) {
    a[i] = true;
    i = i + 1;
  }
  i = 0;
  while (i < N / 2) {
    assert(a[i]);
    i = i + 1;
  }
}

