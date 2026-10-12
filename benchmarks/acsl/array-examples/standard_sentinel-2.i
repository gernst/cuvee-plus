// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

/*@ requires \false;
    assigns \nothing; */
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_sentinel-2.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int main ( ) {
  int a[100000];
  int marker = __VERIFIER_nondet_int();
  int pos = __VERIFIER_nondet_int();
	
	/*@ loop invariant 0 <= i <= 100000;
	    loop assigns i, a[0..99999]; */
	for(int i = 0; i < 100000; i++) 
	{
	  a[i] = __VERIFIER_nondet_int();
	}
	
  if ( pos >= 0 && pos < 100000 ) {
    a[ pos ] = marker;
    int i = 0;
    /*@ loop invariant 0 <= i <= pos;
        loop invariant a[pos] == marker;
        loop assigns i; */
    while( a[ i ] != marker ) {
      i = i + 1;
    }
    __VERIFIER_assert( i <= pos );
  }
  return 0;
}
