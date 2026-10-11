// ./Cuvee.sh -verify -z3 examples/c/parsing/unsigned_nondet.c
// nondeterministic values of unsigned types are nonnegative, those of signed types are not
int main(void) { unsigned int x = __VERIFIER_nondet_uint(); assert(x >= 0); x = __VERIFIER_nondet_ulong(); assert(x >= 0); long long y = (long long) __VERIFIER_nondet_uint() + 1; assert(y > 0); return 0; }
