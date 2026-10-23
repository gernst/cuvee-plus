// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/nla-digbench/cohendiv-ll.c
// SV-COMP nla-digbench/cohendiv-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/cohendiv-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "cohendiv-ll.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  int r = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  assume_abort_if_not(y >= 1);
  q = 0;
  r = x;
  a = 0;
  b = 0;
  while (1 != 0) {
    __VERIFIER_assert(b == y * a);
    __VERIFIER_assert(x == q * y + r);
    if (!(r >= y)) {
      break;
    }
    a = 1;
    b = y;
    while (1 != 0) {
      __VERIFIER_assert(b == y * a);
      __VERIFIER_assert(x == q * y + r);
      __VERIFIER_assert(r >= 0);
      if (!(r >= 2 * b)) {
        break;
      }
      __VERIFIER_assert(r >= 2 * y * a);
      a = 2 * a;
      b = 2 * b;
    }
    r = r - b;
    q = q + a;
  }
  __VERIFIER_assert(x == q * y + r);
  result = 0;
  return result;
}

