// ./Cuvee.sh -teq -simplify -fallback -z3 -verify examples/c/verify/teq_bits_abstract.c
// & on integers other than 0 and 1 stays uninterpreted (bitand, :abstract in the prelude of C): z3 refutes the goal
// by an interpretation of bitand that is not the bitwise and, which is no counterexample, hence unknown, not incorrect
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error(void) { abort(); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); } }
int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = x & 3;
  __VERIFIER_assert(y <= 3);
  return 0;
}
