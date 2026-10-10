// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/Mono4_1.c
// SV-COMP loops-crafted-1/Mono4_1.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/Mono4_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  x = 0;
  y = 500000;
  while (x < N) {
    if (x < 500000) {
      x = x + 1;
    } else {
      x = x + 1;
      y = y + 1;
    }
  }
  assert(y != x);
  result = 0;
  return result;
}

