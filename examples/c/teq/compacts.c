// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/compacts.c
// the positions of the iterations where a[i] == b[i] stored at C[0], C[1], ... (standard_partial_init_ground): the x-th
// of them is at least x and leaves room for the others after it (compacts, select_current_compacts_lower and _upper)
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int b[1000];
  int c[1000];
  int i;
  int j = 0;
  for (i = 0; i < 1000; i++) {
    if (a[i] == b[i]) {
      c[j] = i;
      j = j + 1;
    }
  }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x < j) { __VERIFIER_assert(x <= c[x] && c[x] <= x + i - j); }
  return 0;
}
