// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/deep-nested.c
// SV-COMP loop-simple/deep-nested.yml, translated from benchmarks/sv-comp/dafny/loop-simple/deep-nested.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "deep-nested.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  int d = __VERIFIER_nondet_int();
  int e = __VERIFIER_nondet_int();
  int uint32_max = __VERIFIER_nondet_int();
  uint32_max = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < uint32_max);
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
              __VERIFIER_assert(0);
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

