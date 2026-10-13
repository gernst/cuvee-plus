// ./Cuvee.sh -teq -prove examples/c/teq/inlining.c
// calls of procedures without a contract are inlined, such that the results are known to the caller,
// also through a return inside of a branch, and the variables of the caller with the names of the formals are restored
int inc(int x) { if (x < 0) return 0; return x + 1; }
int main(void) { int x = 5; int y = inc(1); int z = inc(-3); assert(x == 5 && y == 2 && z == 0); return 0; }
