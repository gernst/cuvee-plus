// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/nested_2.c
// SV-COMP loop-simple/nested_2.yml, translated from benchmarks/sv-comp/dafny/loop-simple/nested_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested_2.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  a = N;
  b = N;
  a = 0;
  while (a < N) {
    b = 0;
    while (b < N) {
      b = b + 1;
    }
    a = a + 1;
  }
  __VERIFIER_assert(a == N && b == N);
}

