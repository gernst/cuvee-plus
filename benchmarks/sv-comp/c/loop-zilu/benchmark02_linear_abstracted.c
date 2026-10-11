// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark02_linear_abstracted.c
// SV-COMP loop-zilu/benchmark02_linear_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark02_linear_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark02_linear_abstracted.c", 7, "reach_error"); }
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
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  n = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  i = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  l = tmp_3;
  i = l;
  if (!(l > 0)) {
    result = 0;
    return result;
  }
  if (i < n) {
    i = __VERIFIER_nondet_int();
  }
  if (i < n) {
    assume_abort_if_not(0);
  }
  __VERIFIER_assert(l >= 1);
  result = 0;
  return result;
}

