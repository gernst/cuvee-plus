// ./Cuvee.sh -unbounded examples/c/printing/unbounded_nondet.c
// with -unbounded, nondeterministic values of unsigned types are only nonnegative, those of signed types arbitrary
int main(void) { unsigned int x = __VERIFIER_nondet_uint(); int y = __VERIFIER_nondet_int(); return x + y; }
