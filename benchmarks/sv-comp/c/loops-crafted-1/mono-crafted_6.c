// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/mono-crafted_6.c
// SV-COMP loops-crafted-1/mono-crafted_6.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_6.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int K;
  int x;
  int y;
  int z;
  __VERIFIER_assume(0 < K);
  __VERIFIER_assume(N == 8 * K);
  x = 0;
  y = 4 * K;
  z = 0;
  x = 0;
  while (x < N) {
    if (x < N / 2) {
      x = x + 1;
    } else {
      if (x < 3 * N / 4) {
        x = x + 1;
      } else {
        x = x + 2;
      }
      y = y + 1;
    }
  }
  assert(x == N);
  result = 0;
  return result;
}

