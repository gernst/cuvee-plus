// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-invariants/odd.c
// SV-COMP loop-invariants/odd.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/odd.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "odd.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int x = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  x = 1;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    x = x + 2;
    b = __VERIFIER_nondet_int();
  }
  __VERIFIER_assert(x % 2 == 1);
}

