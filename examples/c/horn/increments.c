// ./Cuvee.sh -chc -prove examples/c/horn/increments.c
// expected: valid
int main(int n) { if (n < 0) return 0; int counter = 0; int x = 0; while (counter++ < n) x++; assert(x == n && counter == n + 1); return 0; }
