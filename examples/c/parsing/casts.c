// ./Cuvee.sh -verify -z3 examples/c/parsing/casts.c
// casts to integer types are the identity, to _Bool a comparison with zero
int main(void) { long long y = (long long) 2 * 3; assert(y == 6); assert((int) -1 == -1); assert((_Bool) 5 == 1); return 0; }
