// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/gj2007b.c
// SV-COMP loop-lit/gj2007b.yml, translated from benchmarks/sv-comp/dafny/loop-lit/gj2007b.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "gj2007b.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int x = __VERIFIER_nondet_int();
  int m = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  x = 0;
  m = 0;
  n = __VERIFIER_nondet_int();
  while (x < n) {
    b = __VERIFIER_nondet_int();
    if (b != 0) {
      m = x;
    }
    x = x + 1;
  }
  __VERIFIER_assert(m >= 0 || n <= 0);
  __VERIFIER_assert(m < n || n <= 0);
}

