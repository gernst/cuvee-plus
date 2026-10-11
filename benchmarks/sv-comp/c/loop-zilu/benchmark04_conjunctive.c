// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-zilu/benchmark04_conjunctive.c
// SV-COMP loop-zilu/benchmark04_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark04_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark04_conjunctive.c", 7, "reach_error"); }
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
  int k = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(n >= 1 && k >= n && j == 0);
  while (j <= n - 1) {
    j = j + 1;
    k = k - 1;
  }
  __VERIFIER_assert(k >= 0);
}

