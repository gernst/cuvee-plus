// ./Cuvee.sh -teq -prove -split -prove -verify examples/c/verify/teq_unsafe.c
// the goal simplifies to false, a refutation without solver, since the steps of -teq are equivalences

extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

int main(void) {
  int x = 0;
  while (x < 10) x++;
  __VERIFIER_assert(x == 11);
  return 0;
}
