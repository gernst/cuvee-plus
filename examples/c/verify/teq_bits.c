// ./Cuvee.sh -teq -simplify -split -simplify -verify examples/c/verify/teq_bits.c
// &, |, ^ on the integers 0 and 1, the truth values that the conditional writes, by the rules of the prelude of C:
// without them, bitand, bitor, bitxor stay uninterpreted, the goals open, and -fallback -z3 refutes them
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error(void) { abort(); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); } }
int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int a = (x < 100 ? 1 : 0) & (y < 100 ? 1 : 0);
  int b = (x < 100 ? 1 : 0) | (y < 100 ? 1 : 0);
  int c = (x < 100 ? 1 : 0) ^ (y < 100 ? 1 : 0);
  __VERIFIER_assert(a == (x < 100 && y < 100 ? 1 : 0));
  __VERIFIER_assert(b == (x < 100 || y < 100 ? 1 : 0));
  __VERIFIER_assert(c == ((x < 100) != (y < 100) ? 1 : 0));
  __VERIFIER_assert((1 & 1) == 1 && (x & 0) == 0 && (0 | x) == x && (1 ^ 1) == 0);
  return 0;
}
