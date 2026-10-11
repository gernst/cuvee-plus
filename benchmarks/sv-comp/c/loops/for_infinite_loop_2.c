// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/for_infinite_loop_2.c
// SV-COMP loops/for_infinite_loop_2.yml, translated from benchmarks/sv-comp/dafny/loops/for_infinite_loop_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "for_infinite_loop_2.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  i = 0;
  x = 0;
  y = 0;
  tmp_1 = __VERIFIER_nondet_int();
  n = tmp_1;
  if (!(n > 0)) {
    result = 0;
    return result;
  }
  i = 0;
  while (1 != 0) {
    __VERIFIER_assert(x == 0);
    i = i + 1;
  }
  __VERIFIER_assert(x != 0);
}

