// ./Cuvee.sh -simplify -chc examples/c/horn/increments.c
// expected: valid
int f(int n) { if (n < 0) return 0; int counter = 0; int x = 0; while (counter++ < n) x++; assert(x == n && counter == n + 1); return 0; }
