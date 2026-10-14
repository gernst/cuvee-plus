// ACSL annotations added by hand (benchmarks/acsl/README.md); the array set is a global
// variable instead of a parameter, since Cuvée passes arrays by value: no element is ever inserted (n stays 0)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "data_structures_set_multi_proc_trivial_ground.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

int set[ 100000 ];
/*@ requires 0 <= size < 100000;
    assigns set[size];
    ensures \result == size + 1;
    ensures set[size] == value;
    ensures \forall integer t; t != size ==> set[t] == \old(set[t]); */
int insert( int size , int value ) {
  set[ size ] = value;
  return size + 1;
}
/*@ requires 0 <= size <= 100000;
    assigns \nothing;
    ensures (\result == 1) <==> (\exists integer t; 0 <= t < size && set[t] == value);
    ensures \result == 1 || \result == 0; */
int elem_exists( int size , int value ) {
  int i;
  /*@ loop invariant 0 <= i <= size;
      loop invariant \forall integer t; 0 <= t < i ==> set[t] != value;
      loop assigns i; */
  for ( i = 0 ; i < size ; i++ ) {
    if ( set[ i ] == value ) return 1;
  }
  return 0;
}
int main( ) {
  int n = 0;
  int x;
  int y;
	
	/*@ loop invariant 0 <= x <= 100000;
	    loop assigns x, set[0..99999]; */
	for (x = 0; x < 100000; x++)
	{
	  set[x] = __VERIFIER_nondet_int();
	}
	
  
	/*@ loop invariant 0 <= x <= n;
	    loop invariant \forall integer p, q; 0 <= p < q < n ==> set[p] != set[q];
	    loop assigns x, y; */
	for ( x = 0 ; x < n ; x++ ) {
    /*@ loop invariant x < y <= n;
        loop invariant \forall integer p, q; 0 <= p < q < n ==> set[p] != set[q];
        loop assigns y; */
    for ( y = x + 1 ; y < n ; y++ ) {
      __VERIFIER_assert( set[ x ] != set[ y ] );
    }
  }
  int values[ 100000 ];
  int v;
	
	/*@ loop invariant 0 <= v <= 100000;
	    loop assigns v, values[0..99999]; */
	for (v = 0; v < 100000; v++)
	{
	  values[v] = __VERIFIER_nondet_int();
	}
  /*@ loop invariant 0 <= v <= 100000;
      loop invariant n == 0;
      loop assigns v, n, set[0..99999]; */
  for ( v = 0 ; v < 100000 ; v++ ) {
    if ( elem_exists( n , values[ v ] ) ) {
      n = insert( n , values[ v ] );
    }
    /*@ loop invariant 0 <= x <= n;
        loop invariant n == 0;
        loop assigns x, y; */
    for ( x = 0 ; x < n ; x++ ) {
      /*@ loop invariant x < y <= n;
          loop assigns y; */
      for ( y = x + 1 ; y < n ; y++ ) {
        __VERIFIER_assert( set[ x ] != set[ y ] );
      }
    }
  }
  /*@ loop invariant 0 <= x <= n;
      loop invariant \forall integer p, q; 0 <= p < q < n ==> set[p] != set[q];
      loop assigns x, y; */
  for ( x = 0 ; x < n ; x++ ) {
    /*@ loop invariant x < y <= n;
        loop invariant \forall integer p, q; 0 <= p < q < n ==> set[p] != set[q];
        loop assigns y; */
    for ( y = x + 1 ; y < n ; y++ ) {
      __VERIFIER_assert( set[ x ] != set[ y ] );
    }
  }
  return 0;
}
