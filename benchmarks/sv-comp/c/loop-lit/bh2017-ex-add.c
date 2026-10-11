// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/bh2017-ex-add.c
// SV-COMP loop-lit/bh2017-ex-add.yml, translated from benchmarks/sv-comp/dafny/loop-lit/bh2017-ex-add.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "bh2017-ex-add.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int m = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  m = 0;
  n = 0;
  while (1) {
    __VERIFIER_assert(m <= 60);
    __VERIFIER_assert(n <= 60);
    b = __VERIFIER_nondet_int();
    c = __VERIFIER_nondet_int();
    if (b != 0 && c != 0) {
      if (m < 60) {
        m = m + 1;
      } else {
        __VERIFIER_assert(m == 60);
        m = 0;
      }
    }
    b = __VERIFIER_nondet_int();
    c = __VERIFIER_nondet_int();
    if (b != 0 && c != 0) {
      if (n < 60) {
        n = n + 1;
      } else {
        __VERIFIER_assert(n == 60);
        n = 0;
      }
    }
  }
}

