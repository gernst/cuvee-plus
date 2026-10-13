// ./Cuvee.sh -teq -prove -rules -verify examples/c/verify/rules.c
// the rules applied by -simplify, (set-info :used ...), are printed on stderr, since -verify does not print the output

extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

int main(void) {
  int x = 0;
  while (x < 10) x++;
  __VERIFIER_assert(x == 10);
  return 0;
}
