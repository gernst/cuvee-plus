// ./Cuvee.sh -teq -prove -split -prove -verify examples/c/verify/teq_safe.c
// the goal is closed by the lemma database, without solver

extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

int main(void) {
  int x = 0;
  while (x < 10) x++;
  __VERIFIER_assert(x == 10);
  return 0;
}
