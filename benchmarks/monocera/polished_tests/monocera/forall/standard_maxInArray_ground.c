// extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

// #define 100000 100000

int main( ) {
  int a[100000];
  int max = 0;
	
	for (int j = 0; j < 100000 ; j++ ) {
    a[j] = __VERIFIER_nondet_int();
  }
	
  int i = 0;
  while ( i < 100000 ) {
    if ( a[i] > max ) {
      max = a[i];
    }
    i = i + 1;
  }
  
  int x;
/*
  for ( x = 0 ; x < 100000 ; x++ ) {
    __VERIFIER_assert(  a[x] <= max  );
  }*/
	//@ assert \forall int jjj; ((0 <= jjj) && (jjj < 100000 )) ==> (  a[jjj] <= max  );

  return 0;
}
