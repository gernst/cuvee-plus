// ./Cuvee.sh -teq -prove -split -prove benchmarks/sv-comp/c/loop-zilu/benchmark09_conjunctive.c
// SV-COMP loop-zilu/benchmark09_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark09_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark09_conjunctive.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  assume_abort_if_not(x == y && y >= 0);
  while (x != 0) {
    x = x - 1;
    y = y - 1;
    if (x < 0 || y < 0) {
      break;
    }
  }
  __VERIFIER_assert(y == 0);
}

