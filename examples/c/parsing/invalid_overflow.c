// ./Cuvee.sh -vcgen -z3 examples/c/parsing/invalid_overflow.c
// the successor of an unsigned integer is not always larger, as it wraps around at UINT_MAX
int main(void) { unsigned int y = __VERIFIER_nondet_uint(); unsigned int z = y + 1; assert(z > y); return 0; }
