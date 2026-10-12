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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_strcpy_ground-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int main( ) {
  int src[100000];
  int dst[100000];
  int i = 0;
  int j = 0;

  /*@ loop invariant 0 <= j <= 100000;
      loop assigns j, src[0..99999]; */
  while ( j < 100000 ) {
    src[j] = __VERIFIER_nondet_int();
    j = j + 1;
  }

  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < i ==> dst[t] == src[t];
      loop assigns i, dst[0..99999]; */
  while ( i < 100000 && src[i] != 0 ) {
    dst[i] = src[i];
    i = i + 1;
  }
  int x;
  /*@ loop invariant 0 <= x <= i;
      loop invariant \forall integer t; 0 <= t < i ==> dst[t] == src[t];
      loop assigns x; */
  for ( x = 0 ; x < i ; x++ ) {
    __VERIFIER_assert( dst[x] == src[x] );
  }
  return 0;
}
