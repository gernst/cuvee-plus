// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark51_polynomial.c
// SV-COMP loop-zilu/benchmark51_polynomial.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark51_polynomial.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark51_polynomial.c", 7, "reach_error"); }
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

void main(void) {
  int x = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  assume_abort_if_not(x >= 0 && x <= 50);
  c = __VERIFIER_nondet_int();
  while (c != 0) {
    if (x > 50) {
      x = x + 1;
    }
    if (x == 0) {
      x = x + 1;
    } else {
      x = x - 1;
    }
    c = __VERIFIER_nondet_int();
  }
  __VERIFIER_assert(x >= 0 && x <= 50);
}

