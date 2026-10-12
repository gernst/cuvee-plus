// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "sanfoundry_10_ground.c", 3, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

/*
 * Adapted from http://www.sanfoundry.com/c-programming-examples-arrays/
 * C program to accept an array of integers and delete the
 * specified integer from the list
 */
int main()
{
    int i;
    int n = 100000;
    int pos;
    int element = __VERIFIER_nondet_int();
    int found = 0;
    int vectorx[n];

		/*@ loop invariant 0 <= i <= n;
		    loop assigns i, vectorx[0..n-1]; */
		for(i = 0; i < n; i++) 
		{
		  vectorx[i] = __VERIFIER_nondet_int();
		} 

    /*@ loop invariant 0 <= i <= n;
        loop invariant found == 0 || found == 1;
        loop invariant found == 0 ==> (\forall integer t; 0 <= t < i ==> vectorx[t] != element);
        loop invariant found == 1 ==> (0 <= pos < i && vectorx[pos] == element && (\forall integer t; 0 <= t < pos ==> vectorx[t] != element));
        loop assigns i, found, pos; */
    for (i = 0; i < n && !found; i++)
    {
        if (vectorx[i] == element)
        {
            found = 1;
            pos = i;
        }
    }
    if ( found )
    {
        /*@ loop invariant pos <= i <= n - 1;
            loop invariant 0 <= pos;
            loop invariant \forall integer t; 0 <= t < pos ==> vectorx[t] != element;
            loop assigns i, vectorx[pos..n-1]; */
        for (i = pos; i <  n - 1; i++)
        {
            vectorx[i] = vectorx[i + 1];
        }
    }
    
    if ( found ) {
      int x;
      /*@ loop invariant 0 <= x <= pos;
          loop invariant \forall integer t; 0 <= t < pos ==> vectorx[t] != element;
          loop assigns x; */
      for ( x = 0 ; x < pos ; x++ ) {
        __VERIFIER_assert(  vectorx[x] != element  );
      }
    }
  return 0;
}
