// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark25_linear.c
// SV-COMP loop-zilu/benchmark25_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark25_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark25_linear.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  if (!(x < 0)) {
    result = 0;
    return result;
  }
  while (x < N) {
    x = x + 1;
  }
  __VERIFIER_assert(x == N);
  result = 0;
  return result;
}

