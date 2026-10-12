// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (a variant of sina4), the loops carry bounds only
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
void reach_error() { __assert_fail("0", "sina4f.c", 10, "reach_error"); }
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
	assume_abort_if_not(N <= 2147483647/sizeof(int));

	int i;
	long long sum[1];
	long long *a = safe_malloc(sizeof(long long)*N);
	long long *b = safe_malloc(sizeof(long long)*N);

	sum[0] = 0;
	/*@ loop invariant 0 <= i <= N;
	    loop assigns i, a[0..N-1]; */
	for(i=0; i<N; i++)
	{
		a[i] = 1;
	}

	/*@ loop invariant 0 <= i <= N;
	    loop assigns i, sum[0]; */
	for(i=0; i<N; i++)
	{
		sum[0] = sum[0] + a[i];
	}

	/*@ loop invariant 0 <= i <= N;
	    loop assigns i, a[0..N-1]; */
	for(i=0; i<N; i++)
	{
		a[i] = a[i] + sum[0];
	}

	/*@ loop invariant 0 <= i <= N;
	    loop assigns i, b[0..N-1]; */
	for(i=0; i<N; i++)
	{
		b[i] = a[i] + 1;
	}

	/*@ loop invariant 0 <= i <= N;
	    loop assigns i,; */
	for(i=0; i<N; i++)
	{
		__VERIFIER_assert(b[i] == N);
	}
	return 1;
}
