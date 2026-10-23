// ./Cuvee.sh -chc -prove examples/c/horn/invalid_conditional_expressions.c
// expected: invalid
int c; int f(void) { c = c + 1; return 1; } int main(void) { int r = 0 ? f() : 2; assert(c == 1); return 0; }
