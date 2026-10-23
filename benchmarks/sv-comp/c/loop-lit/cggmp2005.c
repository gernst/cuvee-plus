// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-lit/cggmp2005.c
// SV-COMP loop-lit/cggmp2005.yml, translated from benchmarks/sv-comp/dafny/loop-lit/cggmp2005.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "cggmp2005.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  i = 1;
  j = 10;
  while (j >= i) {
    i = i + 2;
    j = -1 + j;
  }
  __VERIFIER_assert(j == 6);
}

