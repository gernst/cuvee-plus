// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/nested_1.c
// SV-COMP loop-simple/nested_1.yml, translated from benchmarks/sv-comp/dafny/loop-simple/nested_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested_1.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  a = N;
  a = 0;
  while (a < N) {
    a = a + 1;
  }
  if (a != N) {
    __VERIFIER_assert(0);
  }
  result = 1;
  return result;
}

