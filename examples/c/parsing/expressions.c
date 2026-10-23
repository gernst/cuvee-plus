// ./Cuvee.sh examples/c/parsing/expressions.c
// conversions between integers and truth values, decrements in loop conditions, comparisons of pointers of different
// types, and global variables, whose initial values are the precondition of main and must not call functions
int g = 1;
int truth(int x) { if (x) return !x; else return x && 1; }
int decrement(int n) { while (n-- > 0) ; return n; }
int main(void) { int *p = 0; long *q = 0; char *r = 0; return g + (p == q); }
