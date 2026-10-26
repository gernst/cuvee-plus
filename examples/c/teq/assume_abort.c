// ./Cuvee.sh -teq -prove examples/c/teq/assume_abort.c
// values assumed by assume_abort_if_not in a loop, which C passes as ite(c, 1, 0) != 0: the iteration constraints
// are the conditions themselves, 0 < tmp and tmp < 10 (Simplify.eq_ on conditionals with literal branches); the goal
// remains, since the constraint is not instantiated at the position x (ideas/engine-gaps.md, "Not done")
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
void assume_abort_if_not(int cond) { if (!cond) { abort(); } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int i;
  for (i = 0; i < 1000; i++) {
    int k = __VERIFIER_nondet_int();
    assume_abort_if_not(k > 0 && k < 10);
    a[i] = k;
  }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x < 1000) { __VERIFIER_assert(a[x] > 0); }
  return 0;
}
