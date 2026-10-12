// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (y == x + 1 throughout)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "multivar_1-2.c", 3, "reach_error"); }
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
  unsigned int x = __VERIFIER_nondet_uint();
  unsigned int y = x + 1;

  /*@ loop invariant y == (x + 1) % 4294967296;
      loop assigns x, y; */
  while (x < 1024) {
    x++;
    y++;
  }

  __VERIFIER_assert(x == y);
}
