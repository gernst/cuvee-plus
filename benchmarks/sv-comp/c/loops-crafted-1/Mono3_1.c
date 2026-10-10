// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/Mono3_1.c
// SV-COMP loops-crafted-1/Mono3_1.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/Mono3_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  x = 0;
  y = 0;
  while (x < N) {
    if (x < 500000) {
      y = y + 1;
    } else {
      y = y - 1;
    }
    x = x + 1;
  }
  assert(y != 0);
}

