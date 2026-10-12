// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (a[x] >= a[i] is asserted for x < i)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "sorting_selectionsort_ground-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

int main( ) {
  int a[ 100000 ];
  int i = 0;
  int x;
  int y;
	
	/*@ loop invariant 0 <= i <= 100000;
	    loop assigns i, a[0..99999]; */
	for(int i = 0; i < 100000; i++) 
	{
	    a[i] = __VERIFIER_nondet_int();
	}
	
	i = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop assigns i, k, s, x, y, a[0..99999]; */
  while ( i < 100000 ) {
    int k = i + 1;
    int s = i;
    /*@ loop invariant i <= k <= 100000;
        loop invariant i <= s < 100000;
        loop assigns k, s; */
    while ( k < 100000 ) {
      if ( a[k] < a[s] ) {
        s = k;
      }
      k = k+1;
    }
    if ( s != i ) {
      int tmp = a[s];
      a[s] = a[i];
      a[i] = tmp;
    }
    /*@ loop invariant 0 <= x <= i;
        loop assigns x, y; */
    for ( x = 0 ; x < i ; x++ ) {
      /*@ loop invariant x < y <= i;
          loop assigns y; */
      for ( y = x + 1 ; y < i ; y++ ) {
        __VERIFIER_assert( a[x] <= a[y] );
      }
    }
    /*@ loop invariant i <= x <= 100000;
        loop assigns x; */
    for ( x = 0 ; x < 100000 ; x++ ) {
      __VERIFIER_assert( a[x] >= a[i] );
    }
    i = i+1;
  }
  /*@ loop invariant 0 <= x <= 100000;
      loop assigns x, y; */
  for ( x = 0 ; x < 100000 ; x++ ) {
    /*@ loop invariant x < y <= 100000;
        loop assigns y; */
    for ( y = x + 1 ; y < 100000 ; y++ ) {
      __VERIFIER_assert( a[x] <= a[y] );
    }
  }
  return 0;
}
