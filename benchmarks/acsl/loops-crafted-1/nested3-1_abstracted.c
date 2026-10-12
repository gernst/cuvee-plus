// ACSL annotations added by hand (benchmarks/acsl/README.md); the ranges of the unsigned variables that the loops assign are loop invariants
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
/*@ assigns \nothing; */
extern _Bool __VERIFIER_nondet_bool();
/*@ assigns \nothing; */
extern char __VERIFIER_nondet_char();
/*@ assigns \nothing; */
extern double __VERIFIER_nondet_double();
/*@ assigns \nothing; */
extern float __VERIFIER_nondet_float();
/*@ assigns \nothing; */
extern unsigned long __VERIFIER_nondet_ulong();
/*@ assigns \nothing; */
extern unsigned long long __VERIFIER_nondet_ulonglong();
/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "nested3-1_abstracted.c", 3, "reach_error"); }

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
      loop invariant 0 <= x <= 4294967295;
      loop invariant 0 <= y <= 4294967295;
      loop invariant 0 <= z <= 4294967295;
      loop assigns x, y, z; */
  while (x < 0x0fffffff) {
    y = 0;

    /*@ loop invariant y <= 0x0fffffff;
        loop invariant 0 <= y <= 4294967295;
        loop invariant 0 <= z <= 4294967295;
        loop assigns y, z; */
    while (y < 0x0fffffff) {
   	z =0;
	// START NAIVELOOPABSTRACTION
	if (z < (268435455)) {
	z = __VERIFIER_nondet_uint();
	if (!(z < (268435455))) abort();
	if (z <0x0fffffff) {
		  z++;
		}
	if (z < (268435455)) abort();
	}
	// END NAIVELOOPABSTRACTION
    	__VERIFIER_assert(z % 4);
	y++;
    }
    __VERIFIER_assert(y % 2);

    x++;
  }
  __VERIFIER_assert(x % 2);
  return 0;

}
