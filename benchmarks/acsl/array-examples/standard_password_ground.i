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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_password_ground.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

int main( ) {
  int password[ 100000 ];
  int guess[ 100000 ];
  int i;
  int result = 1;
	
	/*@ loop invariant 0 <= i <= 100000;
	    loop assigns i, password[0..99999], guess[0..99999]; */
	for (i = 0; i < 100000; i++)
	{
	    password[i] = __VERIFIER_nondet_int();
			guess[i] = __VERIFIER_nondet_int();
	}
	
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant result == 0 || result == 1;
      loop invariant result == 1 ==> (\forall integer t; 0 <= t < i ==> password[t] == guess[t]);
      loop assigns i, result; */
  for ( i = 0 ; i < 100000 ; i++ ) {
    if ( password[ i ] != guess[ i ] ) {
      result = 0;
    }
  }
  if ( result ) {
    int x;
    /*@ loop invariant 0 <= x <= 100000;
        loop invariant \forall integer t; 0 <= t < 100000 ==> password[t] == guess[t];
        loop assigns x; */
    for ( x = 0 ; x < 100000 ; x++ ) {
      __VERIFIER_assert( password[ x ] == guess[ x ] );
    }
  }
  return 0;
}
