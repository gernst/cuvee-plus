// ./Cuvee.sh -teq -split -simplify examples/c/teq/invalid_from.c
// the goal is false
int main(void) { unsigned int x = 0; unsigned int z = 5;
  while (x < 10) { if (x >= 5) z++; x++; }
  assert(z != x); return 0; }
