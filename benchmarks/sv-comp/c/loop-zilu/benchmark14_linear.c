// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-zilu/benchmark14_linear.c
// SV-COMP loop-zilu/benchmark14_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark14_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark14_linear.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  i = tmp_1;
  if (!(i >= 0)) {
    result = 0;
    return result;
  }
  while (i > 0) {
    i = i - 1;
  }
  __VERIFIER_assert(i >= 0);
  result = 0;
  return result;
}

