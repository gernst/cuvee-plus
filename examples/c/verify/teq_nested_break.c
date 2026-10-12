// ./Cuvee.sh -teq -simplify -split -simplify -fallback -z3 -verify examples/c/verify/teq_nested_break.c
// the exits of the inner loop, by its test (j == 10 is never reached) and by break (j == 5), are told apart by
// branch conditions, such that the cases of the updates of the outer loop are disjoint; before, both were guarded
// by true and j + 1 == 5, which contradict for j == 4 (x == 4 and x == 5), and z3 proved the false assertion
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error(void) { abort(); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); } }
int main(void) {
  int i = 0;
  int x = 0;
  while (i < 1) {
    i = i + 1;
    int j = 0;
    while (j < 10) {
      j = j + 1;
      if (j == 5) break;
    }
    x = j;
  }
  __VERIFIER_assert(x == 10);
  return 0;
}
