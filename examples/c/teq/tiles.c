// ./Cuvee.sh -teq -include teq:arrays -include teq:strides -prove examples/c/teq/tiles.c
// an outer loop that fills tiles of 3 cells by an inner loop, whose stores are folded (nr3 of SV-COMP, array-tiling):
// the cell i belongs to the tile i / 3 at the position i % 3 (select_current_tiles of teq:strides)
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
    __VERIFIER_assert(a[i] >= 2 || a[i] == 0);
  }
  return 0;
}
