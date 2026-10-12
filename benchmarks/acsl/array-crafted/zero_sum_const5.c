// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "zero_sum_const5.c", 3, "reach_error"); }
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
extern long __VERIFIER_nondet_long(void);
void *malloc(unsigned int size);

long SIZE;

const int MAX = 100000;

int main()
{
	SIZE = __VERIFIER_nondet_long();
	if(SIZE > 1 && SIZE < MAX)
	{
		int i;
		long *a = malloc(sizeof(long)*SIZE);
		long sum=0;

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < i ==> a[t] == 1;
		    loop assigns i, a[0..SIZE-1]; */
		for(i = 0; i < SIZE; i++ )
		{
			a[i] = 1;
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 0*SIZE + i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++ )
		{
			sum = sum + a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 1*SIZE - i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++)
		{
			sum = sum - a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 0*SIZE + i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++ )
		{
			sum = sum + a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 1*SIZE - i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++)
		{
			sum = sum - a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 0*SIZE + i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++ )
		{
			sum = sum + a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 1*SIZE - i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++)
		{
			sum = sum - a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 0*SIZE + i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++ )
		{
			sum = sum + a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 1*SIZE - i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++)
		{
			sum = sum - a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 0*SIZE + i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++ )
		{
			sum = sum + a[i];
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 1;
		    loop invariant sum == 1*SIZE - i;
		    loop assigns i, sum; */
		for(i = 0; i < SIZE; i++)
		{
			sum = sum - a[i];
		}
		__VERIFIER_assert(sum == 0);
	}
	return 1;
}
