// extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

// #define 100000 100000

int main ( ) {
  int a[100000];
  int i = 0;
  while ( i < 100000 ) {
    a[i] = 42;
    i = i + 1;
  }
  
  int x;
/*
  for ( x = 0 ; x < 100000 ; x++ ) {
    __VERIFIER_assert(  a[x] == 42  );
  }*/
	//@ assert \forall int jjj; ((0 <= jjj) && (jjj < 100000 )) ==> (  a[jjj] == 42  );

  return 0;
}
