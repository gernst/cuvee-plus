// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/gr2006.c
// SV-COMP loop-lit/gr2006.yml, translated from benchmarks/sv-comp/dafny/loop-lit/gr2006.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "gr2006.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  x = 0;
  y = 0;
  while (1) {
    if (x < 50) {
      y = y + 1;
    } else {
      y = y - 1;
    }
    if (y < 0) {
      break;
    }
    x = x + 1;
  }
  __VERIFIER_assert(x == 100);
}

