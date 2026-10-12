// ACSL annotations added by hand (benchmarks/acsl/README.md)
//array-reversecopynswap-twice
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "revcpyswp2.c", 4, "reach_error"); }
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
void *safe_malloc(unsigned int size) {
  void *p = malloc(size);
  if (p == 0) {
    abort();
  }
  return p;
}


int SIZE;

const int MAX = 100000;

int main()
{
	SIZE = __VERIFIER_nondet_int();
	if(SIZE > 1 && SIZE < MAX)
	{
		int i;
		int tmp;
		int *a = safe_malloc(sizeof(int)*SIZE);
		int *b = safe_malloc(sizeof(int)*SIZE);
		int *a_copy = safe_malloc(sizeof(int)*SIZE);
		int *b_copy = safe_malloc(sizeof(int)*SIZE);
		
		/*@ loop invariant 0 <= i <= SIZE;
		    loop assigns i, a_copy[0..SIZE-1], b_copy[0..SIZE-1]; */
		for(i=0; i<SIZE; i++)
		{
			a_copy[i] = __VERIFIER_nondet_int();
			b_copy[i] = __VERIFIER_nondet_int();
		}
		
		//reverse copy
		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < i ==> a[t] == a_copy[SIZE-t-1] && b[t] == b_copy[SIZE-t-1];
		    loop assigns i, a[0..SIZE-1], b[0..SIZE-1]; */
		for(i=0; i<SIZE; i++)
		{
			a[i] = a_copy[SIZE-i-1];
			b[i] = b_copy[SIZE-i-1];
		}

		//swap
		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < i ==> a[t] == b_copy[SIZE-t-1] && b[t] == a_copy[SIZE-t-1];
		    loop invariant \forall integer t; i <= t < SIZE ==> a[t] == a_copy[SIZE-t-1] && b[t] == b_copy[SIZE-t-1];
		    loop assigns i, tmp, a[0..SIZE-1], b[0..SIZE-1]; */
		for(i=0; i<SIZE; i++)
		{
			tmp = a[i];
			a[i] = b[i];
			b[i] = tmp;
		}

		//swap
		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < i ==> a[t] == a_copy[SIZE-t-1] && b[t] == b_copy[SIZE-t-1];
		    loop invariant \forall integer t; i <= t < SIZE ==> a[t] == b_copy[SIZE-t-1] && b[t] == a_copy[SIZE-t-1];
		    loop assigns i, tmp, a[0..SIZE-1], b[0..SIZE-1]; */
		for(i=0; i<SIZE; i++)
		{
			tmp = a[i];
			a[i] = b[i];
			b[i] = tmp;
		}

		//assert
		/*@ loop invariant 0 <= i <= SIZE;
		    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == a_copy[SIZE-t-1] && b[t] == b_copy[SIZE-t-1];
		    loop assigns i; */
		for(i=0; i<SIZE; i++)
		{
			__VERIFIER_assert(a[i] == a_copy[SIZE-i-1]);
			//__VERIFIER_assert(b[i] == b_copy[SIZE-i-1]);
		}
	}
	return 1;
}
