// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/as2013-hybrid.c
// SV-COMP loop-lit/as2013-hybrid.yml, translated from benchmarks/sv-comp/dafny/loop-lit/as2013-hybrid.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int i;
  int j;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (1 != 0) {
    i = i + 1;
    j = 0;
    while (j < N) {
      assert(0 <= i);
      assert(i <= N);
      j = j + 1;
    }
    if (i > 9) {
      i = 0;
    }
  }
  result = 0;
  return result;
}

