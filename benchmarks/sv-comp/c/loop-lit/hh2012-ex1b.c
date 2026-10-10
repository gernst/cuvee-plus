// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/hh2012-ex1b.c
// SV-COMP loop-lit/hh2012-ex1b.yml, translated from benchmarks/sv-comp/dafny/loop-lit/hh2012-ex1b.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int i;
  int j;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    j = 0;
    while (j < N) {
      j = j + 1;
      assert(j <= N);
    }
    assert(j == N);
    i = i + 1;
    assert(i <= N);
  }
  assert(i == N);
  result = 0;
  return result;
}

