// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-programs/partial_mod_count_limited_base.c
// SV-COMP array-programs/partial_mod_count_limited_base.yml, translated from benchmarks/sv-comp/dafny/array-programs/partial_mod_count_limited_base.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  int k;
  int a[];
  int R;
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  j = 0;
  k = 0;
  tmp_1 = __VERIFIER_nondet_int();
  R = tmp_1;
  __VERIFIER_assume(R > 0);
  i = 0;
  while (i < N) {
    a[i] = i + 1;
    if (i > N / 2 && k < 1) {
      a[i] = i % R;
    }
    if (a[i] == 0) {
      k = k + 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 0) {
      j = j + 1;
    }
    assert(j < 2);
    i = i + 1;
  }
  result = 0;
  return result;
}

