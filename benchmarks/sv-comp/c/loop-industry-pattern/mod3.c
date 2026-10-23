// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-industry-pattern/mod3.c
// SV-COMP loop-industry-pattern/mod3.yml, translated from benchmarks/sv-comp/dafny/loop-industry-pattern/mod3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "mod3.c", 7, "reach_error"); }
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
  int b = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  assume_abort_if_not(x >= 0);
  y = 1;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    if (x % 3 == 1) {
      x = x + 2;
      y = 0;
    } else {
      if (x % 3 == 2) {
        x = x + 1;
        y = 0;
      } else {
        b = __VERIFIER_nondet_int();
        if (b != 0) {
          x = x + 4;
          y = 1;
        } else {
          x = x + 5;
          y = 1;
        }
      }
    }
    b = __VERIFIER_nondet_int();
  }
  if (y == 0) {
    __VERIFIER_assert(x % 3 == 0);
  }
}

