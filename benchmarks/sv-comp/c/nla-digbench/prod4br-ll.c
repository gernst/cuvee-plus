// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/prod4br-ll.c
// SV-COMP nla-digbench/prod4br-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/prod4br-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "prod4br-ll.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int p = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  assume_abort_if_not(y >= 1);
  a = x;
  b = y;
  p = 1;
  q = 0;
  while (1 != 0) {
    __VERIFIER_assert(q + a * b * p == x * y);
    if (!(a != 0 && b != 0)) {
      break;
    }
    if (a % 2 == 0 && b % 2 == 0) {
      a = a / 2;
      b = b / 2;
      p = 4 * p;
    } else if (a % 2 == 1 && b % 2 == 0) {
      a = a - 1;
      q = q + b * p;
    } else if (a % 2 == 0 && b % 2 == 1) {
      b = b - 1;
      q = q + a * p;
    } else {
      a = a - 1;
      b = b - 1;
      q = q + (a + b + 1) * p;
    }
  }
  __VERIFIER_assert(q == x * y);
  __VERIFIER_assert(a * b == 0);
  result = 0;
  return result;
}

