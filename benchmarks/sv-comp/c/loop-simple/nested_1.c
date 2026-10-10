// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/nested_1.c
// SV-COMP loop-simple/nested_1.yml, translated from benchmarks/sv-comp/dafny/loop-simple/nested_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int a;
  __VERIFIER_assume(0 < N);
  a = N;
  a = 0;
  while (a < N) {
    a = a + 1;
  }
  if (a != N) {
    assert(false);
  }
  result = 1;
  return result;
}

