// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-zilu/benchmark33_linear.c
// SV-COMP loop-zilu/benchmark33_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark33_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark33_linear.c", 7, "reach_error"); }
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
  int N = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  x = __VERIFIER_nondet_int();
  assume_abort_if_not(x >= 0);
  while (x < N && x >= 0) {
    x = x + 1;
  }
  __VERIFIER_assert(x >= N);
}

