// ./Cuvee.sh -verify -z3 examples/c/parsing/unsigned_nondet.c
// nondeterministic values of unsigned types are nonnegative, those of signed types are not
int main(void) { unsigned int x = __VERIFIER_nondet_uint(); assert(x >= 0); x = __VERIFIER_nondet_ulong(); assert(x >= 0); int y = __VERIFIER_nondet_size_t() + 1; assert(y > 0); return 0; }
