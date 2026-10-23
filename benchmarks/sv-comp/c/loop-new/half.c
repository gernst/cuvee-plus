// ./Cuvee.sh -teq -prove -split -prove benchmarks/sv-comp/c/loop-new/half.c
// SV-COMP loop-new/half.yml, translated from benchmarks/sv-comp/dafny/loop-new/half.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "half.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  i = 0;
  n = 0;
  k = __VERIFIER_nondet_int();
  i = 0;
  while (i < 2 * k) {
    if (i % 2 == 0) {
      n = n + 1;
    }
    i = i + 1;
  }
  __VERIFIER_assert(k < 0 || n == k);
}

