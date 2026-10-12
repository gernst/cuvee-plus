// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "underapprox_1-2.c", 3, "reach_error"); }

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
  unsigned int y = 1;

  /*@ loop invariant 0 <= x <= 6;
      loop invariant (x == 0 && y == 1) || (x == 1 && y == 2) || (x == 2 && y == 4) || (x == 3 && y == 8) || (x == 4 && y == 16) || (x == 5 && y == 32) || (x == 6 && y == 64);
      loop assigns x, y; */
  while (x < 6) {
    x++;
    y *= 2;
  }

  __VERIFIER_assert(y % 3);
}
