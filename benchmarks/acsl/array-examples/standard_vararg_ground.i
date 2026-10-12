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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_vararg_ground.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

int main( ){
  int aa [100000];
  int a = 0;
	
	/*@ loop invariant 0 <= i <= 100000;
	    loop assigns i, aa[0..99999]; */
	for(int i = 0; i < 100000; i++)
	{
	  aa[i] = __VERIFIER_nondet_int();
	}
	
  /*@ loop invariant 0 <= a;
      loop invariant \forall integer t; 0 <= t < a ==> aa[t] >= 0;
      loop assigns a; */
  while( aa[a] >= 0 ) {
    a++;
  }
  int x;
  /*@ loop invariant 0 <= x <= a;
      loop invariant \forall integer t; 0 <= t < a ==> aa[t] >= 0;
      loop assigns x; */
  for ( x = 0 ; x < a ; x++ ) {
    __VERIFIER_assert( aa[x] >= 0 );
  }
  return 0;
}
