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
void reach_error() { __assert_fail("0", "ifncomp.c", 10, "reach_error"); }
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

	long long i;
	long long *a = safe_malloc(sizeof(long long)*N);
	long long *b = safe_malloc(sizeof(long long)*N);
	long long *c = safe_malloc(sizeof(long long)*N);

	/*@ loop invariant 0 <= i <= N;
	    loop invariant \forall integer t; 0 <= t < i ==> a[t] == 6*(t+1);
	    loop assigns i, a[0..N-1]; */
	for(i=0; i<N; i++)
	{
		if(i==0) {
			a[0] = 6;
		} else {
			a[i] = a[i-1] + 6;
		}
	}

	/*@ loop invariant 0 <= i <= N;
	    loop invariant \forall integer t; 0 <= t < N ==> a[t] == 6*(t+1);
	    loop invariant \forall integer t; 0 <= t < i ==> b[t] == 3*t*t + 3*t + 1;
	    loop assigns i, b[0..N-1]; */
	for(i=0; i<N; i++)
	{
		if(i==0) {
			b[0] = 1;
		} else {
			b[i] = b[i-1] + a[i-1];
		}
	}

	/*@ loop invariant 0 <= i <= N;
	    loop invariant \forall integer t; 0 <= t < N ==> b[t] == 3*t*t + 3*t + 1;
	    loop invariant \forall integer t; 0 <= t < i ==> c[t] == N + t*t*t;
	    loop assigns i, c[0..N-1]; */
	for(i=0; i<N; i++)
	{
		if(i==0) {
			c[0] = N;
		} else {
			c[i] = c[i-1] + b[i-1];
		}
	}

	/*@ loop invariant 0 <= i <= N;
	    loop invariant \forall integer t; 0 <= t < N ==> c[t] == N + t*t*t;
	    loop assigns i,; */
	for(i=0; i<N; i++)
	{
		__VERIFIER_assert(c[i] == N + i*i*i);
	}
	return 1;
}
