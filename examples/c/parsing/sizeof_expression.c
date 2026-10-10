// ./Cuvee.sh -verify -z3 examples/c/parsing/sizeof_expression.c
// sizeof of variables by their declared types and the sizes of their arrays, also without size by the initializer,
// where parameters that are arrays are addresses (8 bytes in LP64)
char g[10]; void f(int x, int a[]) { assert(sizeof x + sizeof(a) == 12); } int main(void) { int b[2][3]; short c[] = { 1, 2, 3 }; assert(sizeof(g) == 10 && sizeof(b) == 24 && sizeof(b[0]) == 12 && sizeof b[0][0] == 4 && sizeof(c) / sizeof(c[0]) == 3); return 0; }
