// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-new/count_by_1.c
// SV-COMP loop-new/count_by_1.yml, translated from benchmarks/sv-comp/dafny/loop-new/count_by_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "count_by_1.c", 7, "reach_error"); }
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
  assume_abort_if_not(0 < N);
  i = 0;
  while (i < N) {
    i = i + 1;
  }
  __VERIFIER_assert(i == N);
  result = 0;
  return result;
}

