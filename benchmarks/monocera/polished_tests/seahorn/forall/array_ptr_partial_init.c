#include<seahorn/seahorn.h>

typedef unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
//void __VERIFIER_assertWASHERE(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
#define NULL 0
#define SIZE 100000

int *a[SIZE];
int i;
int main ()
{
	for(i = 0; i < SIZE; i++)
	{
		a[i] = NULL;
	}

	for(i = 0; i < SIZE / 2; i++)
	{
		a[i] = malloc(sizeof(int)) ;
	}


	for(i = 0; i < SIZE / 2; i++)
	{
		sassert(a[i] != NULL);
	}

return 0;
}	


