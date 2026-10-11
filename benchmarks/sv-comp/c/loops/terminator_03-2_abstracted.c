// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/terminator_03-2_abstracted.c
// SV-COMP loops/terminator_03-2_abstracted.yml, translated from benchmarks/sv-comp/dafny/loops/terminator_03-2_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "terminator_03-2_abstracted.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  y = tmp_2;
  if (y > 0) {
    if (x < 100) {
      x = __VERIFIER_nondet_int();
    }
    if (x < 100) {
      assume_abort_if_not(0);
    }
  }
  __VERIFIER_assert(y <= 0 || y > 0 && x >= 100);
  result = 0;
  return result;
}

