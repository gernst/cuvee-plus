// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "simple_3-2.c", 3, "reach_error"); }
/*@ assigns \nothing; */
extern unsigned short __VERIFIER_nondet_ushort(void);

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
  unsigned short N = __VERIFIER_nondet_ushort();

  /*@ loop invariant x % 2 == 0;
      loop invariant x <= N + 1;
      loop assigns x; */
  while (x < N) {
    x += 2;
  }

  __VERIFIER_assert(!(x % 2));
}
