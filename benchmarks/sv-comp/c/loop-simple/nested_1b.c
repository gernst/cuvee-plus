// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/nested_1b.c
// SV-COMP loop-simple/nested_1b.yml, translated from benchmarks/sv-comp/dafny/loop-simple/nested_1b.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int a;
  a = 6;
  a = 0;
  while (a < 6) {
    a = a + 1;
  }
  if (a == 6) {
    assert(false);
  }
  result = 1;
  return result;
}

