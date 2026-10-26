// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/stores_cases_point_wrong.c
// the same with a wrong assertion: the copy is compared at the next position, which must leave a goal
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int b[1000];
  int i;
  int z = 500;
  for (i = 0; i < 1000; i++) { a[i] = __VERIFIER_nondet_int(); }
  for (i = 0; i < 1000; i++) {
    if (i != z) {
      b[i] = a[i];
    } else {
      b[i] = a[i];
    }
  }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x < 999) { __VERIFIER_assert(a[x] == b[x + 1]); }
  return 0;
}
