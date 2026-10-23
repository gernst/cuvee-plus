// ./Cuvee.sh -chc -prove examples/c/horn/invalid_conditions.c
// expected: invalid
int c; int f(void) { c = c + 1; return 1; } int main(void) { int r; r = 0 || f(); assert(c == 0); return 0; }
