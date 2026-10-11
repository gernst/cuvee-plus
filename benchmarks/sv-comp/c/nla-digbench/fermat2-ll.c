// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/fermat2-ll.c
// SV-COMP nla-digbench/fermat2-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/fermat2-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "fermat2-ll.c", 7, "reach_error"); }
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
  int A = __VERIFIER_nondet_int();
  int R = __VERIFIER_nondet_int();
  int u = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  int r = __VERIFIER_nondet_int();
  A = __VERIFIER_nondet_int();
  R = __VERIFIER_nondet_int();
  assume_abort_if_not((R - 1) * (R - 1) < A);
  assume_abort_if_not(A % 2 == 1);
  u = 2 * R + 1;
  v = 1;
  r = R * R - A;
  while (1 != 0) {
    __VERIFIER_assert(4 * (A + r) == u * u - v * v - 2 * u + 2 * v);
    if (!(r != 0)) {
      break;
    }
    if (r > 0) {
      r = r - v;
      v = v + 2;
    } else {
      r = r + u;
      u = u + 2;
    }
  }
  __VERIFIER_assert(4 * A == u * u - v * v - 2 * u + 2 * v);
  result = 0;
  return result;
}

