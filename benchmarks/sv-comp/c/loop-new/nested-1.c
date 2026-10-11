// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-new/nested-1.c
// SV-COMP loop-new/nested-1.yml, translated from benchmarks/sv-comp/dafny/loop-new/nested-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested-1.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int m = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  m = __VERIFIER_nondet_int();
  assume_abort_if_not(10 <= n);
  assume_abort_if_not(10 <= m);
  k = 0;
  i = 0;
  while (i < n) {
    j = 0;
    while (j < m) {
      k = k + 1;
      j = j + 1;
    }
    i = i + 1;
  }
  __VERIFIER_assert(k >= 100);
}

