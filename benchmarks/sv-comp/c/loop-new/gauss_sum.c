// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-new/gauss_sum.c
// SV-COMP loop-new/gauss_sum.yml, translated from benchmarks/sv-comp/dafny/loop-new/gauss_sum.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "gauss_sum.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int sum = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(1 <= n);
  sum = 0;
  i = 1;
  while (i <= n) {
    sum = sum + i;
    i = i + 1;
  }
  __VERIFIER_assert(2 * sum == n * (n + 1));
}

