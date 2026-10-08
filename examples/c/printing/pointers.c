// ./Cuvee.sh examples/c/printing/pointers.c
// pointers are printed with the star at the variable, the null pointer as 0
int *g; void *f(int *p) { return 0; } int main(void) { int *q = g; return q == 0; }
