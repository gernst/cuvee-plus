// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-programs/partial_mod_count_4.c
// SV-COMP array-programs/partial_mod_count_4.yml, translated from benchmarks/sv-comp/dafny/array-programs/partial_mod_count_4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int i;
  int j;
  int a[];
  int R;
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  j = 0;
  R = 4;
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
    assert(j < N / 8);
    i = i + 1;
  }
  result = 0;
  return result;
}

