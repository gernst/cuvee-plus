// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (i >> 16 exceeds 250 for large SIZE)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "mlceu.c", 3, "reach_error"); }
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

int main()
{
	SIZE = __VERIFIER_nondet_int();
	if(SIZE <= 0) return 1;
	assume_abort_if_not(SIZE <= 66060288/sizeof(int));

	int i;
	int *a = safe_malloc(sizeof(int)*SIZE);

	/*@ loop invariant 0 <= i <= SIZE;
	    loop invariant \forall integer t; 0 <= t < i ==> a[t] == (t >> 16 > 250 ? 1 : 0);
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
	    loop invariant \forall integer t; 0 <= t < SIZE ==> a[t] == (t >> 16 > 250 ? 1 : 0);
	    loop assigns i; */
	for(i=0; i<SIZE; i++)
	{
		__VERIFIER_assert(a[i] == 0);
	}

	return 1;
}
