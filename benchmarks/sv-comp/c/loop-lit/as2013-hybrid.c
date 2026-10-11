// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/as2013-hybrid.c
// SV-COMP loop-lit/as2013-hybrid.yml, translated from benchmarks/sv-comp/dafny/loop-lit/as2013-hybrid.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "as2013-hybrid.c", 7, "reach_error"); }
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
  int N = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  assume_abort_if_not(10 <= N);
  i = 0;
  while (1 != 0) {
    i = i + 1;
    j = 0;
    while (j < N) {
      __VERIFIER_assert(0 <= i);
      __VERIFIER_assert(i <= N);
      j = j + 1;
    }
    if (i > 9) {
      i = 0;
    }
  }
  result = 0;
  return result;
}

