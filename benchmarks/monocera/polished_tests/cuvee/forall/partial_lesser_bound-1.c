// ./Cuvee.sh -teq -prove benchmarks/monocera/polished_tests/cuvee/forall/partial_lesser_bound-1.c
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
// #define SIZE 10000000
int a[10000000];
int i;
int main()
{
	for(i=0;i<10000000;i++)
	{
	a[i] = 0 ;
	}

	for(i=0;i<10000000/2;i++)
	{
	a[i] = 10 ;
	}


	for(i=0;i<10000000/2;i++)
	{
		__VERIFIER_assert(a[i]==10);
	}
	
	return 0;
}	


