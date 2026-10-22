// ./Cuvee.sh -chc -z3 examples/c/verify/chc_safe.c
// the clauses are satisfiable, the invariant inferred

extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

int main(void) {
  int x = 0;
  while (x < 10) x++;
  __VERIFIER_assert(x == 10);
  return 0;
}
