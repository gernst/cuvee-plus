// ./Cuvee.sh -verify -z3 -unbounded examples/c/parsing/invalid_unbounded_nondet.c
// with -unbounded, nondeterministic values of unsigned types are only nonnegative
int main(void) { unsigned char c = __VERIFIER_nondet_uchar(); assert(c <= 255); return 0; }
