// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "mono-crafted_11.c", 3, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int main() {
  unsigned int x = 0;

  /*@ loop invariant x <= 100000000;
      loop invariant x >= 10000000 ==> x % 2 == 0;
      loop assigns x; */
  while (x < 100000000) {
    if (x < 10000000) {
      x++;
    } else {
      x += 2;
    }
  }

  __VERIFIER_assert((x%2)==0) ;
  return 0;
}
