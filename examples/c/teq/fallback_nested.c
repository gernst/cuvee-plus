// ./Cuvee.sh -teq -prove -split -prove -fallback examples/c/teq/fallback_nested.c
// the nested loops of SV-COMP loop-simple/nested_2: the traces of the inner loop per iteration of the outer one are
// lists of traces, functions of two indices, with a function for the length of each trace
int main(void) { int a = 6; int b = 6; for (a = 0; a < 6; ++a) { for (b = 0; b < 6; ++b) { } } assert(a == 6 && b == 6); return 1; }
