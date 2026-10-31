// ./Cuvee.sh -teq -include teq:aggregation -prove examples/c/teq/max_tie.c
// a maximum and a minimum that take the new value also at a tie (array-1 of SV-COMP, loops): the folds maxs_tie and
// mins_tie, which are maxs and mins (maxs_tie_maxs, mins_tie_mins)
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[10];
  for (int i = 0; i < 10; i++) {
    a[i] = __VERIFIER_nondet_int();
  }
  int hi = a[0];
  int lo = a[0];
  for (int i = 1; i < 10; i++) {
    if (hi <= a[i]) hi = a[i];
    if (a[i] <= lo) lo = a[i];
  }
  for (int j = 0; j < 10; j++) {
    __VERIFIER_assert(lo <= a[j] && a[j] <= hi);
  }
  return 0;
}
