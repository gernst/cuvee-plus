// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark52_polynomial.c
// SV-COMP loop-zilu/benchmark52_polynomial.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark52_polynomial.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark52_polynomial.c", 7, "reach_error"); }
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
  int N = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  assume_abort_if_not(81 < N && N <= 100);
  tmp_1 = __VERIFIER_nondet_int();
  i = tmp_1;
  if (!(i < 10 && i > -10)) {
    result = 0;
    return result;
  }
  while (i * i < N) {
    i = i + 1;
  }
  __VERIFIER_assert(i == 10);
  result = 0;
  return result;
}

