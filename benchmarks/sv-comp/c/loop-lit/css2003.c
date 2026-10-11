// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/css2003.c
// SV-COMP loop-lit/css2003.yml, translated from benchmarks/sv-comp/dafny/loop-lit/css2003.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "css2003.c", 7, "reach_error"); }
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

void main(void) {
  int N = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  i = 1;
  j = 1;
  k = __VERIFIER_nondet_int();
  if (!(0 <= k && k <= 1)) {
    return;
  }
  while (i < N) {
    i = i + 1;
    j = j + k;
    k = k - 1;
    __VERIFIER_assert(1 <= i + k && i + k <= 2 && i >= 1);
  }
}

