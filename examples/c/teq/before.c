// ./Cuvee.sh -teq -split -simplify examples/c/teq/before.c
// the iterations of a counter before and from a bound, counted for a branch on it in the body (gj2007)
int main(void) { int x = 0; int y = 50; int z = 0;
  while (x < 100) { if (x < 50) { x = x + 1; z = z + 1; } else { x = x + 1; y = y + 1; } }
  assert(y == 100 && z == 50); return 0; }
