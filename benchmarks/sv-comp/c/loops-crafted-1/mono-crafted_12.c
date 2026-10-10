// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/mono-crafted_12.c
// SV-COMP loops-crafted-1/mono-crafted_12.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_12.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  int y;
  int z;
  x = 0;
  y = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < y);
  z = 0;
  while (x < y) {
    if (x >= 5000000) {
      z = z + 2;
    }
    x = x + 1;
  }
  assert(!(z % 2 != 0));
  result = 0;
  return result;
}

