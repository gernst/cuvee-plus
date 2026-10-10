// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/nested3-1_abstracted.c
// SV-COMP loops-crafted-1/nested3-1_abstracted.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/nested3-1_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
      if (z < N) {
        z = __VERIFIER_nondet_int();
        __VERIFIER_assume(0 <= z);
        if (!(z < N)) {
          __VERIFIER_assume(false);
        }
        if (z < N) {
          z = z + 1;
        }
        if (z < N) {
          __VERIFIER_assume(false);
        }
      }
      assert(z % 4 != 0);
      y = y + 1;
    }
    assert(y % 2 != 0);
    x = x + 1;
  }
  assert(x % 2 != 0);
  result = 0;
  return result;
}

