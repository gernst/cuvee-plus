// ./Cuvee.sh -verify -z3 examples/c/parsing/chained_assignments.c
int main(void) { int i; int k; i = k = 2; assert(i == 2 && k == 2); return 0; }
