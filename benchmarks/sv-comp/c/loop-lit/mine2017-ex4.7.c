// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-lit/mine2017-ex4.7.c
// SV-COMP loop-lit/mine2017-ex4.7.yml, translated from benchmarks/sv-comp/dafny/loop-lit/mine2017-ex4.7.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "mine2017-ex4.7.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  _Bool tmp_1 = __VERIFIER_nondet_bool();
  _Bool tmp_2 = __VERIFIER_nondet_bool();
  int x = __VERIFIER_nondet_int();
  x = 0;
  while (1) {
    tmp_1 = __VERIFIER_nondet_bool();
    if ((tmp_1 ? 1 : 0) != 0) {
      break;
    }
    __VERIFIER_assert(0 <= x);
    __VERIFIER_assert(x <= 40);
    tmp_2 = __VERIFIER_nondet_bool();
    if ((tmp_2 ? 1 : 0) == 0) {
      x = x + 1;
      if (x > 40) {
        x = 0;
      }
    }
  }
  result = 0;
  return result;
}

