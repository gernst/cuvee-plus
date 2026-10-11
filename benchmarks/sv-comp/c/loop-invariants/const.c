// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invariants/const.c
// SV-COMP loop-invariants/const.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/const.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "const.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int s = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  s = 0;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    if (s != 0) {
      s = s + 1;
    }
    c = __VERIFIER_nondet_int();
    if (c != 0) {
      __VERIFIER_assert(s == 0);
    }
    b = __VERIFIER_nondet_int();
  }
}

