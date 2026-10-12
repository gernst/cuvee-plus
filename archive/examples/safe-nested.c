extern void reach_error(void);
void __VERIFIER_assert(int cond) { if (!cond) reach_error(); }

// nested loops (SV-COMP loop-simple/nested_2), whose goal remains after simplification and is proved by z3 (-fallback)
int main(void) {
  int a = 6;
  int b = 6;
  for (a = 0; a < 6; ++a) {
    for (b = 0; b < 6; ++b) {
    }
  }
  __VERIFIER_assert(a == 6 && b == 6);
  return 0;
}
