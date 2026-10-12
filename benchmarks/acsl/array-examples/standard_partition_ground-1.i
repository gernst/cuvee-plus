// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (cc holds the nonnegative elements)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_partition_ground-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int main( ) {
  int aa[100000];
  int a = 0;
  int b = 0;
  int c = 0;
  int bb[100000];
  int cc[100000];
	
  /*@ loop invariant 0 <= a <= 100000;
      loop invariant 0 <= b <= a;
      loop invariant \forall integer t; 0 <= t < b ==> bb[t] >= 0;
      loop assigns a, b, bb[0..99999]; */
  while( a < 100000 ) {
    aa[ a ] = __VERIFIER_nondet_int();
    if( aa[ a ] >= 0 ) {
      bb[ b ] = aa[ a ];
      b = b + 1;
    }
    a = a + 1;
  }
  a = 0;
  /*@ loop invariant 0 <= a <= 100000;
      loop invariant 0 <= c <= a;
      loop invariant \forall integer t; 0 <= t < c ==> cc[t] >= 0;
      loop invariant \forall integer t; 0 <= t < b ==> bb[t] >= 0;
      loop assigns a, c, cc[0..99999]; */
  while( a < 100000 ) {
    if( aa[ a ] >= 0 ) {
      cc[ c ] = aa[ a ];
      c = c + 1;
    }
    a = a + 1;
  }
  int x;
  /*@ loop invariant 0 <= x <= b;
      loop invariant \forall integer t; 0 <= t < b ==> bb[t] >= 0;
      loop assigns x; */
  for ( x = 0 ; x < b ; x++ ) {
    __VERIFIER_assert( bb[ x ] >= 0 );
  }
  /*@ loop invariant 0 <= x <= c;
      loop invariant \forall integer t; 0 <= t < c ==> cc[t] >= 0;
      loop assigns x; */
  for ( x = 0 ; x < c ; x++ ) {
    __VERIFIER_assert( cc[ x ] < 0 );
  }
  return 0;
}
