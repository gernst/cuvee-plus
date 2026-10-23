// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/nla-digbench/cohencu-ll.c
// SV-COMP nla-digbench/cohencu-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/cohencu-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "cohencu-ll.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  a = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= a);
  n = 0;
  x = 0;
  y = 1;
  z = 6;
  while (1 != 0) {
    __VERIFIER_assert(z == 6 * n + 6);
    __VERIFIER_assert(y == 3 * n * n + 3 * n + 1);
    __VERIFIER_assert(x == n * n * n);
    __VERIFIER_assert(y * z - 18 * x - 12 * y + 2 * z - 6 == 0);
    __VERIFIER_assert(z * z - 12 * y - 6 * z + 12 == 0);
    if (!(n <= a)) {
      break;
    }
    n = n + 1;
    x = x + y;
    y = y + z;
    z = z + 6;
  }
  __VERIFIER_assert(z == 6 * n + 6);
  __VERIFIER_assert(6 * a * x - x * z + 12 * x == 0);
  __VERIFIER_assert(a * z - 6 * a - 2 * y + 2 * z - 10 == 0);
  __VERIFIER_assert(2 * y * y - 3 * x * z - 18 * x - 10 * y + 3 * z - 10 == 0);
  __VERIFIER_assert(z * z - 12 * y - 6 * z + 12 == 0);
  __VERIFIER_assert(y * z - 18 * x - 12 * y + 2 * z - 6 == 0);
  result = 0;
  return result;
}

