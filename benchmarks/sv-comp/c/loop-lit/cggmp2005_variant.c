// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/cggmp2005_variant.c
// SV-COMP loop-lit/cggmp2005_variant.yml, translated from benchmarks/sv-comp/dafny/loop-lit/cggmp2005_variant.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "cggmp2005_variant.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int lo = __VERIFIER_nondet_int();
  int mid = __VERIFIER_nondet_int();
  int hi = __VERIFIER_nondet_int();
  lo = 0;
  mid = __VERIFIER_nondet_int();
  if (!(mid > 0)) {
    result = 0;
    return result;
  }
  hi = 2 * mid;
  while (mid > 0) {
    lo = lo + 1;
    hi = hi - 1;
    mid = mid - 1;
  }
  __VERIFIER_assert(lo == hi);
  result = 0;
  return result;
}

