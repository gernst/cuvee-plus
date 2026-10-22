// ./Cuvee.sh -chc -z3 -entry f examples/c/verify/entry_flag.c
// -entry gives the entry point of a program without main
int f(int n) { if (n < 0) return 0; int x = 0; while (x < n) x++; assert(x == n); return x; }
