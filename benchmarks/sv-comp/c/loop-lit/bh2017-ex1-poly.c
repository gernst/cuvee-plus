// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/bh2017-ex1-poly.c
// SV-COMP loop-lit/bh2017-ex1-poly.yml, translated from benchmarks/sv-comp/dafny/loop-lit/bh2017-ex1-poly.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int i;
  int j;
  i = 0;
  while (i < 4) {
    j = 0;
    while (j < 3) {
      i = i + 1;
      j = j + 2;
      assert(0 <= j);
      assert(j <= 2 * i);
      assert(2 * i <= j + 6);
      assert(j <= 4);
    }
    assert(0 <= j);
    assert(j <= 2 * i);
    assert(2 * i <= j + 6);
    assert(j <= 4);
    i = i - j / 2 + 1;
  }
  result = 0;
  return result;
}

