// ACSL annotations added by hand (benchmarks/acsl/README.md): the partial sums are the logic function sum of the axiomatic Sum
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "zero_sum1.c", 3, "reach_error"); }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern short __VERIFIER_nondet_short(void);

short SIZE;

/*@ axiomatic Sum {
  logic integer sum(short *a, integer n) reads a[0..n-1];
  axiom sum_zero: \forall short *a; sum(a, 0) == 0;
  axiom sum_step: \forall short *a, integer n; n >= 0 ==> sum(a, n+1) == sum(a, n) + a[n];
} */
int main()
{
	SIZE = __VERIFIER_nondet_short();
	if(SIZE > 1)
	{
		int i;
		short a[SIZE];
		long long sum=0;
		
		/*@ loop invariant 0 <= i <= SIZE;
		    loop assigns i, a[0..SIZE-1]; */
		for(int i = 0; i < SIZE; i++) 
		{
		  a[i] = __VERIFIER_nondet_short();
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant sum == 0*sum(a, SIZE) + sum(a, i);
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++ )
		{
			sum = sum + a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant sum == 1*sum(a, SIZE) - sum(a, i);
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++)
		{
			sum = sum - a[i];
		}
		__VERIFIER_assert(sum == 0);
	}
	return 1;
}
