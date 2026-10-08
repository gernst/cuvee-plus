// ./Cuvee.sh -verify -z3 examples/c/parsing/multidimensional.c
int main(void) { int a[2][3]; a[1][2] = 5; a[1][2] += 1; assert(a[1][2] == 6); return 0; }
