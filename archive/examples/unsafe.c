extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

// a loop that ends with x == 10, hence the assertion fails
int main(void) {
  int x = 0;
  while (x < 10) x++;
  __VERIFIER_assert(x == 11);
  return 0;
}
