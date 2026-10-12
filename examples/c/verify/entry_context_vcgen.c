// ./Cuvee.sh -vcgen -z3 -verify examples/c/verify/entry_context_vcgen.c
// -vcgen checks every function against its contract, even without one for all n, which does not hold
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error(void) { abort(); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); } }
void even(int n) { __VERIFIER_assert(n % 2 == 0); }
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x % 2 == 0) {
    even(x);
  }
  return 0;
}
