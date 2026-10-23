// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-lit/mine2017-ex4.6.c
// SV-COMP loop-lit/mine2017-ex4.6.yml, translated from benchmarks/sv-comp/dafny/loop-lit/mine2017-ex4.6.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "mine2017-ex4.6.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int x = __VERIFIER_nondet_int();
  x = 40;
  while (x != 0) {
    __VERIFIER_assert(x <= 40);
    x = x - 1;
    __VERIFIER_assert(x >= 0);
  }
  __VERIFIER_assert(x == 0);
}

