// ./Cuvee.sh -vcgen -z3 -verify examples/c/verify/vcgen_no_invariant.c
// the loop has no invariant, i.e., true, which is too weak: the refuted goal is :abstract, no counterexample

extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

int main(void) {
  int x = 0;
  while (x < 10) x++;
  __VERIFIER_assert(x == 10);
  return 0;
}
