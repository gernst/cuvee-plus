// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/lcm2.c
// SV-COMP nla-digbench/lcm2.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/lcm2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "lcm2.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int u = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  a = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= a);
  b = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= b);
  assume_abort_if_not(a >= 1);
  assume_abort_if_not(b >= 1);
  x = a;
  y = b;
  u = b;
  v = a;
  while (1 != 0) {
    __VERIFIER_assert(x * u + y * v == 2 * a * b);
    if (!(x != y)) {
      break;
    }
    if (x > y) {
      x = x - y;
      v = v + u;
    } else {
      y = y - x;
      u = u + v;
    }
  }
  __VERIFIER_assert(x * u + y * v == 2 * a * b);
  result = 0;
  return result;
}

