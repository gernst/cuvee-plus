// ./Cuvee.sh -chc -prove examples/c/horn/conditional_expressions.c
// expected: valid
// only the branch of ?: that is taken makes its calls and updates
int c; int f(void) { c = c + 1; return 1; } int main(void) { int i = 0; int r = 1 ? f() : i++; assert(c == 1 && i == 0 && r == 1); r = 0 ? f() : i++; assert(c == 1 && i == 1 && r == 0); return 0; }
