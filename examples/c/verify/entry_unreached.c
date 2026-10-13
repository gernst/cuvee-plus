// ./Cuvee.sh -teq -prove -split -prove -verify examples/c/verify/entry_unreached.c
// a function that the entry point main does not call is not checked, its assertion is never reached
extern void abort(void);
void reach_error(void) { abort(); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); } }
void unreached(int n) { __VERIFIER_assert(n == 0); }
int main(void) {
  return 0;
}
