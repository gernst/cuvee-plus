// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/hard-ll.c
// SV-COMP nla-digbench/hard-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/hard-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "hard-ll.c", 7, "reach_error"); }
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
  int r = __VERIFIER_nondet_int();
  int d = __VERIFIER_nondet_int();
  int p = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  A = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= A && A <= 1073741823);
  B = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= B);
  assume_abort_if_not(B >= 1);
  r = A;
  d = B;
  p = 1;
  q = 0;
  while (1 != 0) {
    __VERIFIER_assert(q == 0);
    __VERIFIER_assert(r == A);
    __VERIFIER_assert(d == B * p);
    if (!(r >= d)) {
      break;
    }
    d = 2 * d;
    p = 2 * p;
  }
  while (1 != 0) {
    __VERIFIER_assert(A == q * B + r);
    __VERIFIER_assert(d == B * p);
    if (!(p != 1)) {
      break;
    }
    d = d / 2;
    p = p / 2;
    if (r >= d) {
      r = r - d;
      q = q + p;
    }
  }
  __VERIFIER_assert(A == d * q + r);
  __VERIFIER_assert(B == d);
  result = 0;
  return result;
}

