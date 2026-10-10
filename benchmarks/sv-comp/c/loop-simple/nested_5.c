// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/nested_5.c
// SV-COMP loop-simple/nested_5.yml, translated from benchmarks/sv-comp/dafny/loop-simple/nested_5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int a;
  int b;
  int c;
  int d;
  int e;
  __VERIFIER_assume(0 < N);
  a = N;
  b = N;
  c = N;
  d = N;
  e = N;
  a = 0;
  while (a < N) {
    b = 0;
    while (b < N) {
      c = 0;
      while (c < N) {
        d = 0;
        while (d < N) {
          e = 0;
          while (e < N) {
            e = e + 1;
          }
          d = d + 1;
        }
        c = c + 1;
      }
      b = b + 1;
    }
    a = a + 1;
  }
  if (!(a == N && b == N && c == N && d == N && e == N)) {
    assert(false);
  }
  result = 1;
  return result;
}

