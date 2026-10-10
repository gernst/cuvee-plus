// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-new/count_by_1_variant.c
// SV-COMP loop-new/count_by_1_variant.yml, translated from benchmarks/sv-comp/dafny/loop-new/count_by_1_variant.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int i;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i != N) {
    assert(i <= N);
    i = i + 1;
  }
  result = 0;
  return result;
}

