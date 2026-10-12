// ACSL annotations added by hand (benchmarks/acsl/README.md); the ranges of the unsigned variables that the loops assign are loop invariants
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "functions_1-1.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

/*@ requires z <= 4294967293;
    assigns \nothing;
    ensures \result == z + 2; */
unsigned int f(unsigned int z) {
  return z + 2;
}

int main(void) {
  unsigned int x = 0;

  /*@ loop invariant x % 2 == 0;
      loop invariant x <= 0x10000000;
      loop invariant 0 <= x <= 4294967295;
      loop assigns x; */
  while (x < 0x0fffffff) {
    x = f(x);
  }

  __VERIFIER_assert(!(x % 2));
}
