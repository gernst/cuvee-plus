// ACSL annotations added by hand (benchmarks/acsl/README.md); the ranges of the unsigned variables that the loops assign are loop invariants
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "nested_1-1.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main(void) {
  unsigned int x = 0;
  unsigned int y = 0;

  /*@ loop invariant x <= 0x0fffffff;
      loop invariant 0 <= x <= 4294967295;
      loop invariant 0 <= y <= 4294967295;
      loop assigns x, y; */
  while (x < 0x0fffffff) {
    y = 0;

    /*@ loop invariant 0 <= y <= 10;
        loop invariant x < 0x0fffffff;
        loop assigns y; */
    while (y < 10) {
      y++;
    }

    x++;
  }

  __VERIFIER_assert(x % 2);
}
