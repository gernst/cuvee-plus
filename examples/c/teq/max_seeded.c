// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/max_seeded.c
// a maximum seeded with the first element and continued from the second (sanfoundry_27_ground) bounds all elements
// (current_maxs_seeded_earlier)
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int i;
  for (i = 0; i < 1000; i++) { a[i] = __VERIFIER_nondet_int(); }
  int largest = a[0];
  for (i = 1; i < 1000; i++) {
    if (largest < a[i]) { largest = a[i]; }
  }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x < 1000) { __VERIFIER_assert(largest >= a[x]); }
  return 0;
}
