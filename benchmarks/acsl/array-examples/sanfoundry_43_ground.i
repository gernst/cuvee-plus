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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "sanfoundry_43_ground.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

/*@ assigns dst[0..99999];
    ensures \forall integer t; 0 <= t < 100000 ==> dst[t] == src[t] + 1; */
void incrementArray(int src[100000] , int dst[100000])
{
    int i;
    /*@ loop invariant 0 <= i <= 100000;
        loop invariant \forall integer t; 0 <= t < i ==> dst[t] == src[t] + 1;
        loop assigns i, dst[0..99999]; */
    for (i = 0; i < 100000; i++) {
        dst[i] = src[i]+1;
    }
}
int main()
{
    int src[100000];
    int dst[100000];
				
    /*@ loop invariant 0 <= i <= 100000;
        loop assigns i, src[0..99999]; */
    for (int i = 0; i < 100000; i++) {
        src[i] = __VERIFIER_nondet_int();
    }

    incrementArray( src , dst );
    int x;
    /*@ loop invariant 0 <= x <= 100000;
        loop invariant \forall integer t; 0 <= t < 100000 ==> dst[t] == src[t] + 1;
        loop assigns x;
        loop assigns x, src[0..99999]; */
    for ( x = 0 ; x < 100000 ; x++ ) {
      src[ x ] = dst[ x ]-1;
    }
  return 0;
}
