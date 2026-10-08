// ./Cuvee.sh -teq -split -simplify examples/c/teq/from.c
// the iterations from a bound on, counted for an increment in the body (Mono6_1), where solving z == x for the
// number of iterations would be cyclic, since the count depends on the counter of the iterations
int main(void) { unsigned int x = 0; unsigned int z = 5;
  while (x < 10) { if (x >= 5) z++; x++; }
  assert(z == x); return 0; }
