// ./Cuvee.sh -vcgen -z3 -verify examples/c/verify/vcgen_weak_invariant.c
// the loop invariant holds but is too weak for the assertion, which fails against the specification
extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

int main(void) {
  int x = 0;
  //@ loop invariant 0 <= x;
  while (x < 10) x++;
  __VERIFIER_assert(x == 10);
  return 0;
}
