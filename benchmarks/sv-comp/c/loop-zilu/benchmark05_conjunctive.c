// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark05_conjunctive.c
// SV-COMP loop-zilu/benchmark05_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark05_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark05_conjunctive.c", 7, "reach_error"); }
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
  int y = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(x >= 0 && x <= y && y < n);
  while (x < n) {
    x = x + 1;
    if (x > y) {
      y = y + 1;
    }
  }
  __VERIFIER_assert(y == n);
}

