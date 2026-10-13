// ./Cuvee.sh -teq -prove -split -prove -verify examples/c/verify/entry_context.c
// the entry point is main (as in SV-COMP): even only has a goal inlined at its call, under the condition of the call,
// not one of its own for all n, which would not hold (sanfoundry_24-1)
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
