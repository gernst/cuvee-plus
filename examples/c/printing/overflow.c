// ./Cuvee.sh examples/c/printing/overflow.c
// the overflow of unsigned integers is printed as casts, which parse back to it
int main(void) { unsigned int x = __VERIFIER_nondet_uint(); unsigned char c = x; x = x * 2 - 1; int i = -1; return i < x; }
