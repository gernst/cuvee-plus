// ./Cuvee.sh -vcgen -z3 examples/c/parsing/allocations.c
// memory for n elements is an array, whose elements are arbitrary, or zero for calloc
void *malloc(unsigned int size); void *calloc(unsigned int n, unsigned int size); void free(void *p); int main(void) { int n = 3; int *a = malloc(sizeof(int) * n); a[1] = 2; assert(a[1] == 2); free(a); long *b = (long *) malloc(n * sizeof(long)); b[0] = 1; int *c = calloc(n, sizeof(int)); assert(c[2] == 0); return 0; }
