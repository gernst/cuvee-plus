// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (x is odd)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "simple_4-1.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main(void) {
  unsigned int x = 0x0ffffff1;

  /*@ loop invariant x % 2 == 1;
      loop invariant x >= 1;
      loop assigns x; */
  while (x > 1) {
    x -= 2;
  }

  __VERIFIER_assert(!(x % 2));
}
