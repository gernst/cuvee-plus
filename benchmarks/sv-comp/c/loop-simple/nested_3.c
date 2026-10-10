// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/nested_3.c
// SV-COMP loop-simple/nested_3.yml, translated from benchmarks/sv-comp/dafny/loop-simple/nested_3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int a;
  int b;
  int c;
  __VERIFIER_assume(0 < N);
  a = N;
  b = N;
  c = N;
  a = 0;
  while (a < N) {
    b = 0;
    while (b < N) {
      c = 0;
      while (c < N) {
        c = c + 1;
      }
      b = b + 1;
    }
    a = a + 1;
  }
  if (!(a == N && b == N && c == N)) {
    assert(false);
  }
  result = 1;
  return result;
}

