// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/Mono1_1-1.c
// SV-COMP loops-crafted-1/Mono1_1-1.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/Mono1_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int x;
  __VERIFIER_assume(0 < N);
  x = 0;
  while (x < N) {
    if (x < 10000000) {
      x = x + 1;
    } else {
      x = x + 2;
    }
  }
  assert(x == N + 1);
}

