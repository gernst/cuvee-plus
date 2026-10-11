// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/const_1-2_abstracted.c
// SV-COMP loop-acceleration/const_1-2_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/const_1-2_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "const_1-2_abstracted.c", 7, "reach_error"); }
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
  int y = __VERIFIER_nondet_int();
  int y__VERIFIER_LA_tmp0 = __VERIFIER_nondet_int();
  int __VERIFIER_LA_iterations0 = __VERIFIER_nondet_int();
  int x__VERIFIER_LA_old_tmp0 = __VERIFIER_nondet_int();
  int y__VERIFIER_LA_old_tmp0 = __VERIFIER_nondet_int();
  x = 1;
  y = 0;
  if (y < 1024) {
    y__VERIFIER_LA_tmp0 = y;
    __VERIFIER_LA_iterations0 = (1024 - y__VERIFIER_LA_tmp0) / 1;
    x__VERIFIER_LA_old_tmp0 = x;
    x = __VERIFIER_LA_iterations0 * 0 + x__VERIFIER_LA_old_tmp0 * 0 + 0;
    y__VERIFIER_LA_old_tmp0 = y;
    y = __VERIFIER_LA_iterations0 * 1 + y__VERIFIER_LA_old_tmp0;
  }
  __VERIFIER_assert(x == 1);
}

