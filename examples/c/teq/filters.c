// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/filters.c
// the values of a partitioned by their sign into b and c (standard_partition_original_ground): the first positions of
// each hold the values of their side (filters_above, filters_below)
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int b[1000];
  int c[1000];
  int nb = 0;
  int nc = 0;
  int i;
  for (i = 0; i < 1000; i++) { a[i] = __VERIFIER_nondet_int(); }
  for (i = 0; i < 1000; i++) {
    if (a[i] >= 0) {
      b[nb] = a[i];
      nb = nb + 1;
    } else {
      c[nc] = a[i];
      nc = nc + 1;
    }
  }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x < nb) { __VERIFIER_assert(b[x] >= 0); }
  if (0 <= x && x < nc) { __VERIFIER_assert(c[x] < 0); }
  return 0;
}
