// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (x == 0 after the loop)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "const_1-2.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main(void) {
  unsigned int x = 1;
  unsigned int y = 0;

  /*@ loop invariant y <= 1024;
      loop invariant y > 0 ==> x == 0;
      loop invariant x == 0 || x == 1;
      loop assigns x, y; */
  while (y < 1024) {
    x = 0;
    y++;
  }

  __VERIFIER_assert(x == 1);
}
