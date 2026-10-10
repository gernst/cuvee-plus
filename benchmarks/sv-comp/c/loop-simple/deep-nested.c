// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/deep-nested.c
// SV-COMP loop-simple/deep-nested.yml, translated from benchmarks/sv-comp/dafny/loop-simple/deep-nested.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int a;
  int b;
  int c;
  int d;
  int e;
  int uint32_max;
  uint32_max = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < uint32_max);
  a = 0;
  while (a < uint32_max - 1) {
    b = 0;
    while (b < uint32_max - 1) {
      c = 0;
      while (c < uint32_max - 1) {
        d = 0;
        while (d < uint32_max - 1) {
          e = 0;
          while (e < uint32_max - 1) {
            if (a == b && b == c && c == d && d == e && e == uint32_max - 2) {
              assert(false);
            }
            e = e + 1;
          }
          d = d + 1;
        }
        c = c + 1;
      }
      b = b + 1;
    }
    a = a + 1;
  }
  result = 0;
  return result;
}

