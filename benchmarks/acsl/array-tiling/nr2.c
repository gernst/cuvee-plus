// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "nr2.c", 3, "reach_error"); }
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

int CELLCOUNT;

int main()
{
	CELLCOUNT = __VERIFIER_nondet_int();
	if(CELLCOUNT > 1)
	{
		int DEFAULTVALUE=1;
		int MINVAL=2;
		int i;
		int j;
		int volArray[CELLCOUNT];

		if(CELLCOUNT % 2 != 0) { return 1; }

		assume_abort_if_not(CELLCOUNT % 2 == 0);

		/*@ loop invariant 1 <= i <= CELLCOUNT/2 + 1;
		    loop invariant CELLCOUNT % 2 == 0;
		    loop invariant \forall integer t; 0 <= t < (i-1)*2 ==> volArray[t] >= MINVAL || volArray[t] == 0;
		    loop assigns i, j, volArray[0..CELLCOUNT-1]; */
		for(i = 1; i <= CELLCOUNT/2; i++)
		{
			/*@ loop invariant 0 <= j <= 2;
			    loop invariant 1 <= i <= CELLCOUNT/2;
			    loop invariant \forall integer t; 0 <= t < (i-1)*2 ==> volArray[t] >= MINVAL || volArray[t] == 0;
			    loop invariant \forall integer t; (i-1)*2 <= t < i*2 - j ==> volArray[t] >= MINVAL || volArray[t] == 0;
			    loop assigns j, volArray[0..CELLCOUNT-1]; */
			for(j = 2; j >= 1; j--)
			{
				if(j >= MINVAL)
				{
					volArray[i*2 - j] = j;
				}
				else
				{
					volArray[i*2 - j] = 0;
				}
			}
		}

		/*@ loop invariant 0 <= i <= CELLCOUNT;
		    loop invariant \forall integer t; 0 <= t < CELLCOUNT ==> volArray[t] >= MINVAL || volArray[t] == 0;
		    loop assigns i; */
		for(i = 0; i < CELLCOUNT; i++)
		{
			__VERIFIER_assert(volArray[i] >= MINVAL || volArray[i] == 0 );
		}
	}
	return 1;
}
