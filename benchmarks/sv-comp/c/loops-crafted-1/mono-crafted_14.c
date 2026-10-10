// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/mono-crafted_14.c
// SV-COMP loops-crafted-1/mono-crafted_14.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_14.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int x;
  int y;
  int z;
  __VERIFIER_assume(0 < N);
  x = 0;
  y = 500000;
  z = 0;
  x = 0;
  while (x < N) {
    if (x < 500000) {
      x = x + 1;
    } else {
      x = x + 1;
      y = y + 1;
    }
  }
  while (y > 0) {
    x = x - 1;
    z = z + 1;
    y = y - 2;
  }
  assert(z % 2 == 0);
  assert(x % 2 == 0);
  result = 0;
  return result;
}

