// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/Mono6_1.c
// SV-COMP loops-crafted-1/Mono6_1.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/Mono6_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x;
  int y;
  int z;
  x = 0;
  y = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < y);
  z = 5000000;
  while (x < y) {
    if (x >= 5000000) {
      z = z + 1;
    }
    x = x + 1;
  }
  assert(z != x);
  result = 0;
  return result;
}

