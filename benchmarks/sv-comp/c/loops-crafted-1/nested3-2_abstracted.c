// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/nested3-2_abstracted.c
// SV-COMP loops-crafted-1/nested3-2_abstracted.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/nested3-2_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int x;
  int y;
  int z;
  int w;
  int z__VERIFIER_LA_tmp0;
  int __VERIFIER_LA_iterations0;
  int z__VERIFIER_LA_old_tmp0;
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
        z__VERIFIER_LA_tmp0 = z;
        __VERIFIER_LA_iterations0 = (N - z__VERIFIER_LA_tmp0) / 1;
        z__VERIFIER_LA_old_tmp0 = z;
        z = __VERIFIER_LA_iterations0 * 1 + z__VERIFIER_LA_old_tmp0;
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

