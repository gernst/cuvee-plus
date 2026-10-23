// ./Cuvee.sh -chc -prove examples/c/horn/conditions.c
// expected: valid
// the right operand is evaluated only if the left one does not determine the result
int c; int f(void) { c = c + 1; return 1; } int main(void) { int r; r = 0 && f(); assert(c == 0); r = 1 || f(); assert(c == 0); r = 1 && f(); assert(c == 1 && r); return 0; }
