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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "sanfoundry_02_ground.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

int main()
{
    int array[100000];
    int i;
    int largest1;
    int largest2;
    int temp;
		
		/*@ loop invariant 0 <= i <= 100000;
		    loop assigns i, array[0..99999]; */
		for(i = 0; i < 100000; i++) 
		{
		  array[i] = __VERIFIER_nondet_int();
		}
		
    largest1 = array[0];
    largest2 = array[1];
    if (largest1 < largest2)
    {
        temp = largest1;
        largest1 = largest2;
        largest2 = temp;
    }
    /*@ loop invariant 2 <= i <= 100000;
        loop invariant largest2 <= largest1;
        loop invariant \forall integer t; 0 <= t < i ==> array[t] <= largest1;
        loop invariant \forall integer t; 0 <= t < i ==> array[t] <= largest2 || array[t] == largest1;
        loop assigns i, largest1, largest2; */
    for (i = 2; i < 100000; i++)
    {
        if (array[i] >= largest1)
        {
            largest2 = largest1;
            largest1 = array[i];
        }
        else if (array[i] > largest2)
        {
            largest2 = array[i];
        }
    }
    int x;
    /*@ loop invariant 0 <= x <= 100000;
        loop invariant \forall integer t; 0 <= t < 100000 ==> array[t] <= largest1;
        loop assigns x; */
    for( x = 0 ; x < 100000 ; x++ ) {
      __VERIFIER_assert( array[ x ] <= largest1 );
    }
    /*@ loop invariant 0 <= x <= 100000;
        loop invariant \forall integer t; 0 <= t < 100000 ==> array[t] <= largest2 || array[t] == largest1;
        loop assigns x; */
    for( x = 0 ; x < 100000 ; x++ ) {
      __VERIFIER_assert( array[x] <= largest2 || array[x] == largest1 );
    }
  return 0;
}
