// extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
//void __VERIFIER_assertWASHERE(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

// #define 100000 100000

int main( ){
  int aa [100000]; 
  int a = 0;
	
	for(int i = 0; i < 100000; i++)
	{
	  aa[i] = __VERIFIER_nondet_int();
	}
	
  while( aa[a] >= 0 ) {
    a++;
  }
  
  int x;
  for ( x = 0 ; x < a ; x++ ) {
    assert(  aa[x] >= 0  );
  }
  return 0;
}


