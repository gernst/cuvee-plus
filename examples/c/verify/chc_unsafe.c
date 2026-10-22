// ./Cuvee.sh -chc -z3 examples/c/verify/chc_unsafe.c
// the clauses are unsatisfiable, the assertion fails after the loop

extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

int main(void) {
  int x = 0;
  while (x < 10) x++;
  __VERIFIER_assert(x == 11);
  return 0;
}
