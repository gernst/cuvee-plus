// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (z == 0x0fffffff is not divisible by 4)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "nested3-2.c", 3, "reach_error"); }

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
  unsigned int x = 0;
  unsigned int y = 0;
  unsigned int z = 0;
  unsigned int w = 0;

  /*@ loop invariant x <= 0x0fffffff;
      loop assigns x, y, z; */
  while (x < 0x0fffffff) {
    y = 0;

    /*@ loop invariant y <= 0x0fffffff;
        loop assigns y, z; */
    while (y < 0x0fffffff) {
   	z =0;
	/*@ loop invariant z <= 0x0fffffff;
	    loop assigns z; */
	while (z <0x0fffffff) {
	  z++;
	}
    	__VERIFIER_assert(!(z % 4));
	y++;
    }
    __VERIFIER_assert(!(y % 2));

    x++;
  }
  __VERIFIER_assert(!(x % 2));
 return 0;

}
