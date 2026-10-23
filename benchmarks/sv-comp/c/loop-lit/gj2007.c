// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-lit/gj2007.c
// SV-COMP loop-lit/gj2007.yml, translated from benchmarks/sv-comp/dafny/loop-lit/gj2007.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "gj2007.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  assume_abort_if_not(50 <= N);
  x = 0;
  y = 50;
  while (x < N) {
    if (x < 50) {
      x = x + 1;
    } else {
      x = x + 1;
      y = y + 1;
    }
  }
  __VERIFIER_assert(y == N);
}

