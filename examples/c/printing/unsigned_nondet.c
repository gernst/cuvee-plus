// ./Cuvee.sh examples/c/printing/unsigned_nondet.c
// nondeterministic values of unsigned types are nonnegative, which is assumed after the value
int main(void) { unsigned int x = __VERIFIER_nondet_uint(); return x; }
