// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/mono-crafted_1.c
// SV-COMP loops-crafted-1/mono-crafted_1.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  int y;
  int z;
  __VERIFIER_assume(50000 <= N);
  x = 0;
  y = 50000;
  z = 0;
  x = 0;
  while (x < N) {
    if (x < 50000) {
      x = x + 1;
    } else {
      x = x + 1;
      y = y + 1;
    }
  }
  while (y > z) {
    y = y - 1;
    x = x - 1;
  }
  assert(x == z);
}

