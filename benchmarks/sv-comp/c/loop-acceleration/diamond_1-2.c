// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-acceleration/diamond_1-2.c
// SV-COMP loop-acceleration/diamond_1-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/diamond_1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "diamond_1-2.c", 7, "reach_error"); }
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
  assume_abort_if_not(0 < N);
  x = 0;
  y = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= y);
  while (x < N) {
    if (y % 2 == 0) {
      x = x + 1;
    } else {
      x = x + 2;
    }
  }
  __VERIFIER_assert(x % 2 == y % 2);
}

