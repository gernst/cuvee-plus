// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "rewrev.c", 3, "reach_error"); }
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

const int MAX = 100000;
int SIZE;

int main()
{
	SIZE = __VERIFIER_nondet_int();
	if(SIZE > 1 && SIZE < MAX)
	{
		int i;
		int *a = malloc(sizeof(int)*SIZE);
		int val2 = 3;
		int val1 = 7;
		int low=2;

		/*@ loop invariant -2 <= i <= SIZE-2;
		    loop invariant \forall integer t; i+2 <= t < SIZE ==> a[t] == val2;
		    loop invariant val2 == 3 && low == 2;
		    loop assigns i, a[0..SIZE-1]; */
		for(i=SIZE-2; i >= -1; i--)
		{
			if(i >= 0)
			{
				a[i] = val1;
			}
			a[i+1] = val2;
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == val2;
		    loop invariant val2 == 3 && low == 2;
		    loop assigns i; */
		for(i = 0; i < SIZE; i++)
		{
			__VERIFIER_assert(a[i] >= low);
		}
	}
	return 1;
}
