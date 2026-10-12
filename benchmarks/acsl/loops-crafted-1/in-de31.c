// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "in-de31.c", 3, "reach_error"); }
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

int main()
{
  unsigned int n = __VERIFIER_nondet_uint();
  unsigned int x=n, y=0, z;
  /*@ loop invariant x + y == n;
      loop assigns x, y; */
  while(x>0)
  {
    x--;
    y++;
  }

  z = y;
  /*@ loop invariant x + z == n;
      loop invariant y == n;
      loop assigns x, z; */
  while(z>0)
  {
    x++;
    z--;
  }

  /*@ loop invariant y + z == n;
      loop assigns y, z; */
  while(y>0)
  {
    y--;
    z++;
  }

  __VERIFIER_assert(z==n);
  return 0;
}
