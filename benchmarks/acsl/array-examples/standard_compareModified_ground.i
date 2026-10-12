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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_compareModified_ground.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

int main( ) {
  int a[100000];
  int b[100000];
  int i = 0;
  int c [100000];
  int rv = 1;
	
	/*@ loop invariant 0 <= j <= 100000;
	    loop assigns j, a[0..99999], b[0..99999]; */
	for (int j = 0; j < 100000 ; j++ ) {
    a[j] = __VERIFIER_nondet_int();
		b[j] = __VERIFIER_nondet_int();
  }
	
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant rv == 0 || rv == 1;
      loop invariant rv == 1 ==> (\forall integer t; 0 <= t < i ==> a[t] == b[t]);
      loop invariant \forall integer t; 0 <= t < i ==> c[t] == a[t];
      loop assigns i, rv, c[0..99999]; */
  while ( i < 100000 ) {
    if ( a[i] != b[i] ) {
      rv = 0;
    }
    c[i] = a[i];
    i = i+1;
  }
  int x;
  if ( rv ) {
    /*@ loop invariant 0 <= x <= 100000;
        loop invariant \forall integer t; 0 <= t < 100000 ==> a[t] == b[t];
        loop assigns x; */
    for ( x = 0 ; x < 100000 ; x++ ) {
      __VERIFIER_assert( a[x] == b[x] );
    }
  }
  /*@ loop invariant 0 <= x <= 100000;
      loop invariant \forall integer t; 0 <= t < 100000 ==> c[t] == a[t];
      loop assigns x; */
  for ( x = 0 ; x < 100000 ; x++ ) {
    __VERIFIER_assert( a[x] == c[x] );
  }
  return 0;
}
