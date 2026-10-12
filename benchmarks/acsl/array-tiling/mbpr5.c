// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "mbpr5.c", 3, "reach_error"); }
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
		int MINVAL=2;
		int i;
		int volArray[CELLCOUNT];
		int CCCELVOL5 = 8;
		int CCCELVOL4 = 5;
		int CCCELVOL3 = 7;
		int CCCELVOL2 = 3;
		int CCCELVOL1 = 1;

		if(CELLCOUNT % 5 != 0) { return 1; }

		assume_abort_if_not(CELLCOUNT % 5 == 0);
		/*@ loop invariant 1 <= i <= CELLCOUNT/5 + 1;
		    loop invariant CELLCOUNT % 5 == 0;
		    loop invariant \forall integer t; 0 <= t < CELLCOUNT ==> t % 5 < 0 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop invariant \forall integer t; 0 <= t < (i-1)*5 ==> t % 5 == 0 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop assigns i, volArray[0..CELLCOUNT-1]; */
		for(i = 1; i <= CELLCOUNT/5; i++)
		{
			if(CCCELVOL5 >= MINVAL)
			{
				volArray[i*5 - 5] = CCCELVOL5;
			}
			else
			{
				volArray[i*5 - 5] = 0;
			}
			volArray[i*5 - 4] = volArray[i*5 - 4];
			volArray[i*5 - 3] = volArray[i*5 - 3];
			volArray[i*5 - 2] = volArray[i*5 - 2];
			volArray[i*5 - 1] = volArray[i*5 - 1];
		}

		/*@ loop invariant 1 <= i <= CELLCOUNT/5 + 1;
		    loop invariant CELLCOUNT % 5 == 0;
		    loop invariant \forall integer t; 0 <= t < CELLCOUNT ==> t % 5 < 1 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop invariant \forall integer t; 0 <= t < (i-1)*5 ==> t % 5 == 1 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop assigns i, volArray[0..CELLCOUNT-1]; */
		for(i = 1; i <= CELLCOUNT/5; i++)
		{
			if(CCCELVOL4 >= MINVAL)
			{
				volArray[i*5 - 4] = CCCELVOL4;
			}
			else
			{
				volArray[i*5 - 4] = 0;
			}
			volArray[i*5 - 5] = volArray[i*5 - 5];
			volArray[i*5 - 3] = volArray[i*5 - 3];
			volArray[i*5 - 2] = volArray[i*5 - 2];
			volArray[i*5 - 1] = volArray[i*5 - 1];
		}

		/*@ loop invariant 1 <= i <= CELLCOUNT/5 + 1;
		    loop invariant CELLCOUNT % 5 == 0;
		    loop invariant \forall integer t; 0 <= t < CELLCOUNT ==> t % 5 < 2 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop invariant \forall integer t; 0 <= t < (i-1)*5 ==> t % 5 == 2 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop assigns i, volArray[0..CELLCOUNT-1]; */
		for(i = 1; i <= CELLCOUNT/5; i++)
		{
			if(CCCELVOL3 >= MINVAL)
			{
				volArray[i*5 - 3] = CCCELVOL3;
			}
			else
			{
				volArray[i*5 - 3] = 0;
			}
			volArray[i*5 - 5] = volArray[i*5 - 5];
			volArray[i*5 - 4] = volArray[i*5 - 4];
			volArray[i*5 - 2] = volArray[i*5 - 2];
			volArray[i*5 - 1] = volArray[i*5 - 1];
		}

		/*@ loop invariant 1 <= i <= CELLCOUNT/5 + 1;
		    loop invariant CELLCOUNT % 5 == 0;
		    loop invariant \forall integer t; 0 <= t < CELLCOUNT ==> t % 5 < 3 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop invariant \forall integer t; 0 <= t < (i-1)*5 ==> t % 5 == 3 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop assigns i, volArray[0..CELLCOUNT-1]; */
		for(i = 1; i <= CELLCOUNT/5; i++)
		{
			if(CCCELVOL2 >= MINVAL)
			{
				volArray[i*5 - 2] = CCCELVOL2;
			}
			else
			{
				volArray[i*5 - 2] = 0;
			}
			volArray[i*5 - 5] = volArray[i*5 - 5];
			volArray[i*5 - 4] = volArray[i*5 - 4];
			volArray[i*5 - 3] = volArray[i*5 - 3];
			volArray[i*5 - 1] = volArray[i*5 - 1];
		}

		/*@ loop invariant 1 <= i <= CELLCOUNT/5 + 1;
		    loop invariant CELLCOUNT % 5 == 0;
		    loop invariant \forall integer t; 0 <= t < CELLCOUNT ==> t % 5 < 4 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop invariant \forall integer t; 0 <= t < (i-1)*5 ==> t % 5 == 4 ==> (volArray[t] >= MINVAL || volArray[t] == 0);
		    loop assigns i, volArray[0..CELLCOUNT-1]; */
		for(i = 1; i <= CELLCOUNT/5; i++)
		{
			if(CCCELVOL1 >= MINVAL)
			{
				volArray[i*5 - 1] = CCCELVOL1;
			}
			else
			{
				volArray[i*5 - 1] = 0;
			}
			volArray[i*5 - 5] = volArray[i*5 - 5];
			volArray[i*5 - 4] = volArray[i*5 - 4];
			volArray[i*5 - 3] = volArray[i*5 - 3];
			volArray[i*5 - 2] = volArray[i*5 - 2];
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

