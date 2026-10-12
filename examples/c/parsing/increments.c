// ./Cuvee.sh -vcgen -z3 examples/c/parsing/increments.c
// the value of x++ is the old one, that of ++x the new one, the update is made before the expression
int main(void) { int i = 0; int a[3]; a[i++] = 5; assert(i == 1 && a[0] == 5); int j = ++i; assert(j == 2 && i == 2); int k = i--; assert(k == 2 && i == 1); assert(--i == 0); return 0; }
