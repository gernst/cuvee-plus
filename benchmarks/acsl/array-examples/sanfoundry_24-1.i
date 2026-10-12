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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "sanfoundry_24-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ requires i % 2 == 0;
    assigns \nothing; */
void printEven( int i ) {
  __VERIFIER_assert( ( i % 2 ) == 0 );
}
/*@ requires i % 2 != 0;
    assigns \nothing; */
void printOdd( int i ) {
  __VERIFIER_assert( ( i % 2 ) != 0 );
}
int main()
{
    int array[100000];
    int i;
    int num = __VERIFIER_nondet_int();
		
		/*@ loop invariant 0 <= i;
		    loop invariant i <= num || i == 0;
		    loop assigns i, array[0..99999]; */
		for(i = 0; i < num; i++) 
		{
		  array[i] = __VERIFIER_nondet_int();
		}
		
    /*@ loop invariant 0 <= i;
        loop invariant i <= num || i == 0;
        loop assigns i; */
    for (i = 0; i < num; i++)
    {
        if (array[i] % 2 == 0)
        {
            printEven( array[i] );
        }
    }
    /*@ loop invariant 0 <= i;
        loop invariant i <= num || i == 0;
        loop assigns i; */
    for (i = 0; i < num; i++)
    {
        if (array[i] % 2 != 0)
        {
            printOdd( array[i] );
        }
    }
  return 0;
}
