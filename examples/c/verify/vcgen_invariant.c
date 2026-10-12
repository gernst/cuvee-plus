// ./Cuvee.sh -vcgen -z3 -verify examples/c/verify/vcgen_invariant.c
// the loop invariant is strong enough for the assertion
extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

int main(void) {
  int x = 0;
  //@ loop invariant 0 <= x <= 10;
  while (x < 10) x++;
  __VERIFIER_assert(x == 10);
  return 0;
}
