// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/sqrt1-ll.c
// SV-COMP nla-digbench/sqrt1-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/sqrt1-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sqrt1-ll.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void assume_abort_if_not(int cond) {
  if (!(cond != 0)) {
    assume_abort_if_not(0);
  }
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  int s = __VERIFIER_nondet_int();
  int t = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  a = 0;
  s = 1;
  t = 1;
  while (1 != 0) {
    __VERIFIER_assert(t == 2 * a + 1);
    __VERIFIER_assert(s == (a + 1) * (a + 1));
    __VERIFIER_assert(t * t - 4 * s + 2 * t + 1 == 0);
    if (!(s <= n)) {
      break;
    }
    a = a + 1;
    t = t + 2;
    s = s + t;
  }
  __VERIFIER_assert(t == 2 * a + 1);
  __VERIFIER_assert(s == (a + 1) * (a + 1));
  __VERIFIER_assert(t * t - 4 * s + 2 * t + 1 == 0);
  result = 0;
  return result;
}

