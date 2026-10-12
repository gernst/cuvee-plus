// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*
 * Benchmarks contributed by Divyesh Unadkat[1,2], Supratik Chakraborty[1], Ashutosh Gupta[1]
 * [1] Indian Institute of Technology Bombay, Mumbai
 * [2] TCS Innovation labs, Pune
 *
 */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "s42if.c", 10, "reach_error"); }
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
void* malloc(unsigned int size);
void *safe_malloc(unsigned int size) {
  void *p = malloc(size);
  if (p == 0) {
    abort();
  }
  return p;
}


int N;

int main()
{
	N = __VERIFIER_nondet_int();
	if(N <= 0) return 1;
	int check_size = sizeof(int) > 5 ? sizeof(int) : 5;
	assume_abort_if_not(N <= 2147483647 / check_size);

	int i;
	long long sum[1];
	int *a = safe_malloc(sizeof(int)*N);

	sum[0] = 0;
	/*@ loop invariant 0 <= i <= N;
	    loop invariant \forall integer t; 0 <= t < i ==> a[t] == 1;
	    loop assigns i, a[0..N-1]; */
	for(i=0; i<N; i++)
	{
		a[i] = 1;
	}

	/*@ loop invariant 0 <= i <= N;
	    loop invariant \forall integer t; 0 <= t < i ==> a[t] == 5;
	    loop invariant \forall integer t; i <= t < N ==> a[t] == 1;
	    loop assigns i, a[0..N-1]; */
	for(i=0; i<N; i++)
	{
		if(a[i] == 1) {
			a[i] = a[i] + 4;
		} else {
			a[i] = a[i] - 1;
		}
	}

	/*@ loop invariant 0 <= i <= N;
	    loop invariant \forall integer t; 0 <= t < N ==> a[t] == 5;
	    loop invariant sum[0] == 5*i;
	    loop assigns i, sum[0]; */
	for(i=0; i<N; i++)
	{
		if(a[i] == 5)
		{
			sum[0] = sum[0] + a[i];
		} else {
			sum[0] = sum[0] * a[i];
		}
	}

	__VERIFIER_assert(sum[0] == 5*N);
	return 1;
}
