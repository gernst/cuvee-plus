// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (the elements beyond n are arbitrary and may equal the removed element)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "check_removal_from_set_after_insertion.c", 3, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

const int SIZE = 100000;
/* 
   Implements a set. Inserts elements from an array of values into the set. Then removes an element from the set and then checks that the removed item is not present in the set.
*/


/*@ requires 0 <= size < SIZE;
    assigns set[size];
    ensures \result == size + 1;
    ensures set[size] == value; */
int insert( int set [] , int size , int value ) {
  set[ size ] = value;
  return size + 1;
}

/*@ requires 0 <= size <= SIZE;
    assigns \nothing;
    ensures (\result == 1) <==> (\exists integer t; 0 <= t < size && set[t] == value); */
int elem_exists( int set [ ] , int size , int value ) {
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
  int i, pos, n = 0, found = 0;
  int set[ SIZE ];       // set for storing values
  int values[ SIZE ];    // array of values to be inserted in the array
  int element;           // element to be removed

 	/*@ loop invariant 0 <= i <= SIZE;
 	    loop assigns i, values[0..SIZE-1]; */
 	for ( i = 0 ; i < SIZE ; i++ ) {
		set[i] = __VERIFIER_nondet_int();
		values[i] = __VERIFIER_nondet_int();
	}
	
	element = __VERIFIER_nondet_int(); 

  int v;
  /*@ loop invariant 0 <= v <= SIZE;
      loop invariant 0 <= n <= v;
      loop invariant \forall integer p, q; 0 <= p < q < n ==> set[p] != set[q];
      loop assigns v, n, set[0..SIZE-1]; */
  for ( v = 0 ; v < SIZE ; v++ ) {
    if ( elem_exists( set , n , values[ v ] ) != 1 ) {
      // parametes are passed by reference
      n = insert( set , n , values[ v ] );
    }
  }
  

    /*@ loop invariant 0 <= i <= SIZE;
        loop invariant found == 0 || found == 1;
        loop invariant found == 0 ==> (\forall integer t; 0 <= t < i ==> set[t] != element);
        loop invariant found == 1 ==> (0 <= pos < i && set[pos] == element && (\forall integer t; 0 <= t < pos ==> set[t] != element));
        loop assigns i, found, pos; */
    for (i = 0; i < SIZE && found != 1; i++) {
        if (set[i] == element)
        {
            found = 1;
            pos = i;
        }
    }
    if ( found == 1 )
    {
        /*@ loop invariant pos <= i <= SIZE - 1;
            loop invariant 0 <= pos;
            loop invariant \forall integer t; 0 <= t < pos ==> set[t] != element;
            loop assigns i, set[pos..SIZE-1]; */
        for (i = pos; i <  SIZE - 1; i++)
        {
            set[i] = set[i + 1];
        }
    }

    if(found == 1) 
    {
      /*@ loop invariant 0 <= i <= SIZE - 1;
          loop invariant \forall integer t; 0 <= t < pos ==> set[t] != element;
          loop assigns i; */
      for(i=0; i < SIZE - 1; i++)
      {
        __VERIFIER_assert(set[i] != element);
      }
    }
}
