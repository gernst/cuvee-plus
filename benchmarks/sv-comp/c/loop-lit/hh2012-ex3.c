// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/hh2012-ex3.c
// SV-COMP loop-lit/hh2012-ex3.yml, translated from benchmarks/sv-comp/dafny/loop-lit/hh2012-ex3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int i;
  int j;
  i = 0;
  while (i < 4) {
    j = 0;
    while (j < 4) {
      i = i + 1;
      j = j + 1;
      assert(0 <= j);
      assert(j <= i);
      assert(i <= j + 3);
      assert(j <= 4);
    }
    assert(0 <= j);
    assert(j <= i);
    assert(i <= j + 3);
    assert(j <= 4);
    i = i - j + 1;
  }
  result = 0;
  return result;
}

