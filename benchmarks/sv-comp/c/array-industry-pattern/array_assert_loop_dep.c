// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/array_assert_loop_dep.c
// SV-COMP array-industry-pattern/array_assert_loop_dep.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_assert_loop_dep.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    a[i] = 10;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == 10);
    if (i + 1 != 15000) {
      a[i + 1] = 20;
    }
    i = i + 1;
  }
}

