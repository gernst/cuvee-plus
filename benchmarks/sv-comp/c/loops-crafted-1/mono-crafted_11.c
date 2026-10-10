// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loops-crafted-1/mono-crafted_11.c
// SV-COMP loops-crafted-1/mono-crafted_11.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_11.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int K;
  int x;
  __VERIFIER_assume(0 < K);
  __VERIFIER_assume(N == 20 * K);
  x = 0;
  while (x < N) {
    if (x < 2 * K) {
      x = x + 1;
    } else {
      x = x + 2;
    }
  }
  assert(x % 2 == 0);
  result = 0;
  return result;
}

