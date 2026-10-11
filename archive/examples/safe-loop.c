extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

// a loop up to a nondeterministic bound, whose sum is twice the number of its iterations
int main(void) {
  int n = __VERIFIER_nondet_int();
  int i = 0;
  int s = 0;
  while (i < n) {
    s = s + 2;
    i = i + 1;
  }
  __VERIFIER_assert(n <= 0 || s == 2 * n);
  return 0;
}
