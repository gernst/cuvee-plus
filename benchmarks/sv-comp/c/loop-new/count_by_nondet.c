// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-new/count_by_nondet.c
// SV-COMP loop-new/count_by_nondet.yml, translated from benchmarks/sv-comp/dafny/loop-new/count_by_nondet.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "count_by_nondet.c", 7, "reach_error"); }
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
  int k = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  i = 0;
  k = 0;
  while (i < N) {
    j = __VERIFIER_nondet_int();
    assume_abort_if_not(1 <= j && j < N);
    i = i + j;
    k = k + 1;
  }
  __VERIFIER_assert(k <= N);
}

