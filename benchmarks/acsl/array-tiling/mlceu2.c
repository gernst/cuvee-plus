// ACSL annotations added by hand (benchmarks/acsl/README.md): i >> 16 stays 0 or 1 below MAX
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "mlceu2.c", 3, "reach_error"); }
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
extern int __VERIFIER_nondet_int(void);
void *malloc(unsigned int size);

int SIZE;

const int MAX = 100000;

int main()
{
	SIZE = __VERIFIER_nondet_int();
	if(SIZE > 1 && SIZE < MAX)
	{
		int i;
		int *a = malloc(sizeof(int)*SIZE);

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant SIZE < 100000;
		    loop invariant \forall integer t; 0 <= t < i ==> a[t] == 0;
		    loop assigns i, a[0..SIZE-1]; */
		for(i=0; i<SIZE; i++)
		{
			if( i>>16 > 250)
			{
				a[i] = 1;
			}
			else
			{
				a[i] = 0;
			}
		}

		//assert
		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == 0;
		    loop assigns i; */
		for(i=0; i<SIZE; i++)
		{
			__VERIFIER_assert(a[i] == 0);
		}
	}
	return 1;
}
