// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-programs/partial_mod_count_2.c
// SV-COMP array-programs/partial_mod_count_2.yml, translated from benchmarks/sv-comp/dafny/array-programs/partial_mod_count_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int R;
  int a[];
  __VERIFIER_assume(0 < N);
  j = 0;
  R = 2;
  i = 0;
  while (i < N) {
    a[i] = i + 1;
    if (i > N / 2) {
      a[i] = i % R;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 0) {
      j = j + 1;
    }
    assert(j < N / 4);
    i = i + 1;
  }
}

