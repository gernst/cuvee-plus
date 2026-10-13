// ./Cuvee.sh -teq -prove -split -prove examples/c/teq/unsigned_phases.c
// an unsigned variable whose updates are remainders in two cases is in the range of unsigned int, which the updates
// assume, such that under the test of the loop they are the sums themselves, as for mathematical integers
int main(void) { unsigned int x = 0;
  while (x < 100000000) { if (x < 10000000) x = x + 1; else x = x + 2; }
  assert(x == 100000000); return 0; }
