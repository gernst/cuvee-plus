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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_partial_init_ground.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

int main ( ) {
  int A[ 100000 ];
  int B[ 100000 ];
  int C[ 100000 ];
  int i;
  int j = 0;
	
  /*@ loop invariant 0 <= i <= 100000;
      loop assigns i, A[0..99999], B[0..99999]; */
  for (i = 0; i < 100000 ; i++) {
    A[i] = __VERIFIER_nondet_int();
    B[i] = __VERIFIER_nondet_int();
  }	
	
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant 0 <= j <= i;
      loop invariant \forall integer t; 0 <= t < j ==> t <= C[t] <= t + i - j;
      loop assigns i, j, C[0..99999]; */
  for (i = 0; i < 100000 ; i++) {
    if ( A[i] == B[i] ) {
      C[j] = i;
      j = j + 1;
    }
  }
  int x;
  /*@ loop invariant 0 <= x <= j;
      loop invariant 0 <= j <= i;
      loop invariant \forall integer t; 0 <= t < j ==> t <= C[t] <= t + i - j;
      loop assigns x; */
  for ( x = 0 ; x < j ; x++ ) {
    __VERIFIER_assert( C[x] <= x + i - j );
  }
  /*@ loop invariant 0 <= x <= j;
      loop invariant \forall integer t; 0 <= t < j ==> t <= C[t];
      loop assigns x; */
  for ( x = 0 ; x < j ; x++ ) {
    __VERIFIER_assert( C[x] >= x );
  }
  return 0;
}
