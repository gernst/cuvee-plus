// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark25_linear_abstracted.c
// SV-COMP loop-zilu/benchmark25_linear_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark25_linear_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark25_linear_abstracted.c", 7, "reach_error"); }
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
  int tmp_1 = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  if (!(x < 0)) {
    result = 0;
    return result;
  }
  if (x < 10) {
    x = __VERIFIER_nondet_int();
    if (!(x < 10)) {
      assume_abort_if_not(0);
    }
    if (x < 10) {
      x = x + 1;
    }
    if (x < 10) {
      assume_abort_if_not(0);
    }
  }
  __VERIFIER_assert(x == 10);
  result = 0;
  return result;
}

