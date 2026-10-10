// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/nested5-2.c
// SV-COMP loops-crafted-1/nested5-2.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/nested5-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int M;
  int x;
  int y;
  int z;
  int w;
  int v;
  __VERIFIER_assume(0 < N);
  __VERIFIER_assume(0 < M);
  x = 0;
  y = 0;
  z = 0;
  w = 0;
  v = 0;
  w = 0;
  while (w < N) {
    x = 0;
    while (x < M) {
      y = 0;
      while (y < M) {
        z = 0;
        while (z < M) {
          v = 0;
          while (v < N) {
            v = v + 1;
          }
          assert(!(v % 4 != 0));
          z = z + 1;
        }
        y = y + 1;
      }
      x = x + 1;
    }
    w = w + 1;
  }
  result = 0;
  return result;
}

