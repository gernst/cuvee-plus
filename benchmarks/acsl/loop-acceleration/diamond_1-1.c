// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "diamond_1-1.c", 3, "reach_error"); }
/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint(void);

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
  unsigned int y = __VERIFIER_nondet_uint();

  /*@ loop invariant x <= 100;
      loop invariant y % 2 == 0 ==> x % 2 == 0;
      loop invariant y % 2 != 0 ==> x <= 99;
      loop assigns x; */
  while (x < 99) {
    if (y % 2 == 0) {
      x += 2;
    } else {
      x++;
    }
  }

  __VERIFIER_assert((x % 2) == (y % 2));
}
