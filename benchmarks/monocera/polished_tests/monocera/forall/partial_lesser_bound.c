// extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
void *malloc(unsigned int size);
// #define 1000000 1000000
// #define 0 0
int *a[1000000];
int i;
int main()
{
	for(i = 0; i < 1000000; i++)
	{
		a[i] = 0;
	}

	for(i = 0; i < 1000000 / 2; i++)
	{
		a[i] = malloc(sizeof(int)) ;
	}
/*


	for(i = 0; i < 1000000 / 2; i++)
	{
		__VERIFIER_assert(a[i] != 0);
	}*/
	//@ assert \forall int jjj; ((0 <= jjj) && (jjj < 1000000 / 2)) ==> (a[jjj] != 0);

	return 0;
}	

