// ./Cuvee.sh -vcgen -z3 examples/c/parsing/invalid_malloc.c
void *malloc(unsigned int size); int main(void) { int *a = malloc(sizeof(int) * 2); assert(a[0] == 0); return 0; }
