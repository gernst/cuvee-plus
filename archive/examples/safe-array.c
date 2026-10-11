extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

// an array initialized by a loop, read at a nondeterministic position within it
int main(void) {
  int n = __VERIFIER_nondet_int();
  int a[n];
  for (int i = 0; i < n; i++) a[i] = 0;
  int j = __VERIFIER_nondet_int();
  if (0 <= j && j < n) __VERIFIER_assert(a[j] == 0);
  return 0;
}
