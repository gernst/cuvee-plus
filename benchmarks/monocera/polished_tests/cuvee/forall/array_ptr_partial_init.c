// ./Cuvee.sh -teq -simplify benchmarks/monocera/polished_tests/cuvee/forall/array_ptr_partial_init.c
typedef unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
// #define NULL 0
// #define SIZE 100000

int *a[100000];
int i;
int main ()
{
	for(i = 0; i < 100000; i++)
	{
		a[i] = 0;
	}

	for(i = 0; i < 100000 / 2; i++)
	{
		a[i] = malloc(sizeof(int)) ;
	}


	for(i = 0; i < 100000 / 2; i++)
	{
		__VERIFIER_assert(a[i] != 0);
	}

return 0;
}	


