// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-zilu/benchmark23_conjunctive.c
// SV-COMP loop-zilu/benchmark23_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark23_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark23_conjunctive.c", 7, "reach_error"); }
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
  assume_abort_if_not(0 < N);
  i = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  assume_abort_if_not(i == 0 && j == 0);
  while (i < N) {
    j = j + 2;
    i = i + 1;
  }
  __VERIFIER_assert(j == 2 * N);
}

