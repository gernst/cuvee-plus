// ./Cuvee.sh -print null examples/c/parsing/invalid_acsl_separated.c
// annotations of ACSL without counterparts, e.g. on memory, are not supported
/*@ requires \separated(a, b); */
int first(int *a, int *b) { return 0; }
int main(void) { return 0; }
