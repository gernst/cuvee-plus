// ./Cuvee.sh -teq -prove -split -prove -quiet examples/c/verify/exit.c
// exit ends the program like abort, so the assertion holds on the paths that continue

extern void reach_error(void);
extern void exit(int);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }
extern int __VERIFIER_nondet_int(void);

int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x < 0) exit(0);
  __VERIFIER_assert(x >= 0);
  return 0;
}
