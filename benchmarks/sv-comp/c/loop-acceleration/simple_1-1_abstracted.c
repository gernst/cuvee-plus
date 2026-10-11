// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_1-1_abstracted.c
// SV-COMP loop-acceleration/simple_1-1_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_1-1_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_1-1_abstracted.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int x__VERIFIER_LA_tmp0 = __VERIFIER_nondet_int();
  int __VERIFIER_LA_iterations0 = __VERIFIER_nondet_int();
  int x__VERIFIER_LA_old_tmp0 = __VERIFIER_nondet_int();
  x = 0;
  if (x < 268435455) {
    x__VERIFIER_LA_tmp0 = x;
    __VERIFIER_LA_iterations0 = (268435455 - x__VERIFIER_LA_tmp0) / 2;
    x__VERIFIER_LA_old_tmp0 = x;
    x = __VERIFIER_LA_iterations0 * 2 + x__VERIFIER_LA_old_tmp0;
  }
  __VERIFIER_assert(x % 2 != 0);
}

