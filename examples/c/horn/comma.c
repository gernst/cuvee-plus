// ./Cuvee.sh -simplify -chc examples/c/horn/comma.c
// expected: valid
int main(void) { int i; int j; for (i = 0, j = 4; i < j; i++, j--) ; assert(i == j); return 0; }
