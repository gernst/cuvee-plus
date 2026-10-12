// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "pnr3.c", 3, "reach_error"); }
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

/*@ assigns \nothing; */
int ReadFromPort()
{
	int x = __VERIFIER_nondet_int();
	return x;
}

int SIZE;

const int MAX = 100000;

int main()
{
	SIZE = __VERIFIER_nondet_int();
	if(SIZE > 1 && SIZE < MAX)
	{
		int i;
		int value;
		int *a = malloc(sizeof(int)*SIZE);
		int DEFAULTVAL = 0; 
		int FIXEDVAL = 10; 

		if(SIZE % 3 != 0) { return 1; }

		assume_abort_if_not(SIZE % 3 == 0);
		/*@ loop invariant 1 <= i <= SIZE/3 + 1;
		    loop invariant SIZE % 3 == 0;
		    loop invariant \forall integer t; 0 <= t < (i-1)*3 ==> a[t] != DEFAULTVAL;
		    loop invariant DEFAULTVAL == 0 && FIXEDVAL == 10;
		    loop assigns i, value, a[0..SIZE-1]; */
		for (i = 1 ; i <= SIZE/3 ; i++)
		{
			value = ReadFromPort();	
			if(value != DEFAULTVAL)
			{
				a[i*3 - 3] = value ;   
			}
			else 
			{
				a[i*3 - 3] = FIXEDVAL;  
			}

			value = ReadFromPort();	
			if(value != DEFAULTVAL)
			{
				a[i*3 - 2] = value ;   
			}
			else 
			{
				a[i*3 - 2] = FIXEDVAL;  
			}

			value = ReadFromPort();	
			if(value != DEFAULTVAL)
			{
				a[i*3 - 1] = value ;   
			}
			else 
			{
				a[i*3 - 1] = FIXEDVAL;  
			}
		}

		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] != DEFAULTVAL;
		    loop assigns i; */
		for ( i = 0; i < SIZE; i++)  
		{
			__VERIFIER_assert(a[i]!=DEFAULTVAL);
		}
	}
	return 1;
}
