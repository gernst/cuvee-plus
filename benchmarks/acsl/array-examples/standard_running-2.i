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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "standard_running-2.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

int main ( ) {
  int a[100000];
  int b[100000];
  int i = 0;
	
	/*@ loop invariant 0 <= i <= 100000;
	    loop assigns i, a[0..99999]; */
	for(i = 0; i< 100000; i++) 
	{ 
	    a[i] = __VERIFIER_nondet_int();
	}
	
	i = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant \forall integer t; 0 <= t < i ==> b[t] == (a[t] >= 0 ? 1 : 0);
      loop assigns i, b[0..99999]; */
  while ( i < 100000 ) {
    if ( a[i] >= 0 ) b[i] = 1;
    else b[i] = 0;
    i = i + 1;
  }
  int f = 1;
  i = 0;
  /*@ loop invariant 0 <= i <= 100000;
      loop invariant f == 1;
      loop invariant \forall integer t; 0 <= t < 100000 ==> b[t] == (a[t] >= 0 ? 1 : 0);
      loop assigns i, f; */
  while ( i < 100000 ) {
    if ( a[i] >= 0 && !b[i] ) f = 0;
    if ( a[i] < 0 && b[i] ) f = 0;
    i = i + 1;
  }
  __VERIFIER_assert ( f );
  return 0;
}
