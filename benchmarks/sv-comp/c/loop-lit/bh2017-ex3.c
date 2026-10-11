// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/bh2017-ex3.c
// SV-COMP loop-lit/bh2017-ex3.yml, translated from benchmarks/sv-comp/dafny/loop-lit/bh2017-ex3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "bh2017-ex3.c", 7, "reach_error"); }
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
  _Bool tmp_3 = __VERIFIER_nondet_bool();
  int m = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  m = 0;
  n = 0;
  while (1 != 0) {
    __VERIFIER_assert(m <= 60);
    __VERIFIER_assert(n <= 60);
    tmp_1 = __VERIFIER_nondet_bool();
    if (tmp_1) {
      tmp_2 = __VERIFIER_nondet_bool();
      if (tmp_2) {
        if (m < 60) {
          m = m + 1;
        } else {
          __VERIFIER_assert(m == 60);
          m = 0;
        }
      }
    } else {
      tmp_3 = __VERIFIER_nondet_bool();
      if (tmp_3) {
        if (n < 60) {
          n = n + 1;
        } else {
          __VERIFIER_assert(n == 60);
          n = 0;
        }
      }
    }
  }
  result = 0;
  return result;
}

