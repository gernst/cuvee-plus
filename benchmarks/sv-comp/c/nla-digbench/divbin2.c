// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/divbin2.c
// SV-COMP nla-digbench/divbin2.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/divbin2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "divbin2.c", 7, "reach_error"); }
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
  int B = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  int r = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  A = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= A);
  B = 1;
  q = 0;
  r = A;
  b = B;
  while (1 != 0) {
    if (!(r >= b)) {
      break;
    }
    b = 2 * b;
  }
  while (1 != 0) {
    __VERIFIER_assert(A == q * b + r);
    if (!(b != B)) {
      break;
    }
    q = 2 * q;
    b = b / 2;
    if (r >= b) {
      q = q + 1;
      r = r - b;
    }
  }
  __VERIFIER_assert(A == q * b + r);
  result = 0;
  return result;
}

