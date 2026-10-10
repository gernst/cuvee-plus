// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/nested3-2.c
// SV-COMP loops-crafted-1/nested3-2.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/nested3-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int x;
  int y;
  int z;
  int w;
  __VERIFIER_assume(0 < N);
  x = 0;
  y = 0;
  z = 0;
  w = 0;
  while (x < N) {
    y = 0;
    while (y < N) {
      z = 0;
      while (z < N) {
        z = z + 1;
      }
      assert(!(z % 4 != 0));
      y = y + 1;
    }
    assert(!(y % 2 != 0));
    x = x + 1;
  }
  assert(!(x % 2 != 0));
  result = 0;
  return result;
}

