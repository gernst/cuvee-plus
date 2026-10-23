// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-acceleration/nested_1-1.c
// SV-COMP loop-acceleration/nested_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/nested_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested_1-1.c", 7, "reach_error"); }
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
  int M = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N && N % 2 == 1);
  assume_abort_if_not(0 < M);
  x = 0;
  y = 0;
  while (x < N) {
    y = 0;
    while (y < M) {
      y = y + 1;
    }
    x = x + 1;
  }
  __VERIFIER_assert(x % 2 != 0);
}

