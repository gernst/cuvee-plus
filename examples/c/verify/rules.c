// ./Cuvee.sh -teq -prove -rules examples/c/verify/rules.c
// the rules applied by -prove, (set-info :used ...), are printed with the output

extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

int main(void) {
  int x = 0;
  while (x < 10) x++;
  __VERIFIER_assert(x == 10);
  return 0;
}
