// ./Cuvee.sh -teq -include teq:arrays -include teq:strides -prove examples/c/teq/tiles_wrong.c
// the same with a wrong assertion: the last cell of each tile is 0, which must remain
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) { if (!(cond)) { reach_error(); } }
int main()
{
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 1000) return 0;
  int a[3 * n];
  for (int i = 1; i <= n; i++) {
    for (int j = 3; j >= 1; j--) {
      if (j >= 2) {
        a[i * 3 - j] = j;
      } else {
        a[i * 3 - j] = 0;
      }
    }
  }
  for (int i = 0; i < 3 * n; i++) {
    __VERIFIER_assert(a[i] >= 2);
  }
  return 0;
}
