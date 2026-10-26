// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/max_prefix.c
// the maximum and the minimum of the values that a loop stores bound each of them (standard_maxInArray_ground,
// standard_minInArray_ground-2): the loops read the values as the prefix of their list (maps_earlier), the assertions
// read the list (current_maxs_prefix_earlier, current_mins_prefix_earlier)
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int i;
  for (i = 0; i < 1000; i++) { a[i] = __VERIFIER_nondet_int(); }
  int max = 0;
  int min = 0;
  for (i = 0; i < 1000; i++) {
    if (a[i] > max) { max = a[i]; }
  }
  for (i = 0; i < 1000; i++) {
    if (a[i] < min) { min = a[i]; }
  }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x < 1000) { __VERIFIER_assert(a[x] <= max && min <= a[x]); }
  return 0;
}
