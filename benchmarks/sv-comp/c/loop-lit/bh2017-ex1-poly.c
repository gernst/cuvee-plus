// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/bh2017-ex1-poly.c
// SV-COMP loop-lit/bh2017-ex1-poly.yml, translated from benchmarks/sv-comp/dafny/loop-lit/bh2017-ex1-poly.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "bh2017-ex1-poly.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  i = 0;
  while (i < 4) {
    j = 0;
    while (j < 3) {
      i = i + 1;
      j = j + 2;
      __VERIFIER_assert(0 <= j);
      __VERIFIER_assert(j <= 2 * i);
      __VERIFIER_assert(2 * i <= j + 6);
      __VERIFIER_assert(j <= 4);
    }
    __VERIFIER_assert(0 <= j);
    __VERIFIER_assert(j <= 2 * i);
    __VERIFIER_assert(2 * i <= j + 6);
    __VERIFIER_assert(j <= 4);
    i = i - j / 2 + 1;
  }
  result = 0;
  return result;
}

