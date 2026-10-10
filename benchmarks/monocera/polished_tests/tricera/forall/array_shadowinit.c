// extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
//void __VERIFIER_assertWASHERE(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*
  The program initializes the array 'a' in a loop having loop counter 'i' with a variable 'k' which is a shadow of 'i'. Checks universally quantified property \forall i, a[i] = i.
*/

// #define main main

extern int __VERIFIER_nondet_int(void);

int N;
int main() {
 N=__VERIFIER_nondet_int();
 if(N>0) {
  int i,k;
  int a[N];

  i=0;
  k=0;
  while(i < N) {
   a[k]=k;
   i=i+1;
   k=k+1;
  }

  i=0;
  while(i < N) {
   assert(a[i]==i);
   i=i+1;
  }
 }
 return 0;
}
