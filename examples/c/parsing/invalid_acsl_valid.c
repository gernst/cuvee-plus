// ./Cuvee.sh -print null examples/c/parsing/invalid_acsl_valid.c
// annotations of ACSL without counterparts, e.g. on memory, are not supported
/*@ requires \valid(a + (0..n-1)); */
int first(int *a, int n) { return a[0]; }
int main(void) { return 0; }
