// ./Cuvee.sh -vcgen -z3 examples/c/parsing/initializer_lists.c
// the elements that are not given are zero
int g[3] = {1, 2}; int main(void) { int a[2][2] = {{1, 2}, {3}}; assert(a[1][0] == 3 && a[1][1] == 0 && g[1] == 2 && g[2] == 0); return 0; }
