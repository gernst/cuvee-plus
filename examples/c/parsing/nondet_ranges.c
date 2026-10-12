// ./Cuvee.sh -vcgen -z3 -arch 32 examples/c/parsing/nondet_ranges.c
// nondeterministic values are within the ranges of their types, where long has 4 bytes in ILP32
int main(void) { unsigned char c = __VERIFIER_nondet_uchar(); assert(c <= 255); short s = __VERIFIER_nondet_short(); assert(-32768 <= s && s <= 32767); long l = __VERIFIER_nondet_long(); assert(l <= 2147483647); return 0; }
